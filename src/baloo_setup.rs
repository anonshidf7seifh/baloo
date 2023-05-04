/*
This file includes the setup algorithm for Baloo with multi openings.
A full description of the setup is not formally given in the paper.
*/

use ark_ec::{AffineCurve,ProjectiveCurve, msm::VariableBaseMSM};
use ark_poly::{  UVPolynomial, GeneralEvaluationDomain,
        EvaluationDomain, univariate::DensePolynomial};
use ark_bls12_381::{Fr, FrParameters,G1Affine, G2Affine, G1Projective,G2Projective};
use ark_ff::{Fp256, UniformRand};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};

use crate::tools::{UniPoly381, convert_to_bigints};
use std::{time::{Instant}, fs::File, io::Read};

use crate::multiopen::multiple_open_g1;


// structure of public parameters
#[allow(non_snake_case)]
pub struct PublicParameters {
    pub domain_m: GeneralEvaluationDomain<Fr>,
    pub domain_n: GeneralEvaluationDomain<Fr>,
    pub domain_N: GeneralEvaluationDomain<Fr>,
    pub N: usize,
    pub m: usize,
    pub n: usize,
    pub g1_powers: Vec<G1Affine>,
    pub g2_powers: Vec<G2Affine>,
    pub g1_zH: G1Affine,
}

// store and load the g1_powers and g2_powers of the public parameters
impl PublicParameters{
    //store powers of g in a file
    pub fn store(&self, path: &str) {
        use std::io::Write;
        let mut f = File::create(path).expect("Unable to create file");

        //1. g1 powers
        let mut g1_powers_bytes = vec![];
        let deg_g1_powers: u32 = self.g1_powers.len().try_into().unwrap();
        let deg_g1_powers_bytes = deg_g1_powers.to_be_bytes();
        f.write_all(&deg_g1_powers_bytes).expect("Unable to write data");
        let deg_g1_powers_32: usize = deg_g1_powers.try_into().unwrap();
        for i in 0..deg_g1_powers_32
        {
            self.g1_powers[i].into_projective().into_affine().serialize_uncompressed(&mut g1_powers_bytes).ok();
        }
        f.write_all(&g1_powers_bytes).expect("Unable to write data");

        //2. g2 powers
        let mut g2_bytes = vec![];
        let deg2: u32 = self.g2_powers.len().try_into().unwrap();
        let deg2_bytes = deg2.to_be_bytes();
        f.write_all(&deg2_bytes).expect("Unable to write data");
        let deg2_32: usize = deg2.try_into().unwrap();
        for i in 0..deg2_32
        {
            self.g2_powers[i].into_projective().into_affine().serialize_uncompressed(&mut g2_bytes).ok();
        }
        f.write_all(&g2_bytes).expect("Unable to write data");

    }

    //load powers of g from a file
    pub fn load(path: &str)
    ->(
        Vec<G1Affine>,
        Vec<G2Affine>
    )
     {
        const G1_UNCOMPR_SIZE: usize =96;
        const G2_UNCOMPR_SIZE: usize =192;
        let mut data = Vec::new();
        let mut f = File::open(path).expect("Unable to open file");
        f.read_to_end(&mut data).expect("Unable to read data");
        let mut cur_counter: usize  = 0;

        //1. reading G1 powers
        let deg_g1_powers_bytes: [u8; 4] = (&data[cur_counter..cur_counter+4]).try_into().unwrap();
        let deg_g1_powers: u32 = u32::from_be_bytes(deg_g1_powers_bytes);
        let mut g1_powers = vec![];
        let deg_g1_powers_32: usize = deg_g1_powers.try_into().unwrap();
        cur_counter += 4;
        for _ in 0..deg_g1_powers_32
        {
            let buf_bytes = &data[cur_counter ..cur_counter+G1_UNCOMPR_SIZE];
            let tmp = G1Affine::deserialize_unchecked(buf_bytes).unwrap();
            g1_powers.push(tmp);
            cur_counter+=G1_UNCOMPR_SIZE;
        }

        //2. reading G2 powers
        let deg2_bytes: [u8; 4] = (&data[cur_counter..cur_counter+4]).try_into().unwrap();
        let deg2: u32 = u32::from_be_bytes(deg2_bytes);
        let mut g2_powers = vec![];
        let deg2_32: usize = deg2.try_into().unwrap();
        cur_counter += 4;
        for _ in 0..deg2_32
        {
            let buf_bytes = &data[cur_counter ..cur_counter+G2_UNCOMPR_SIZE];
            let tmp = G2Affine::deserialize_unchecked(buf_bytes).unwrap();
            g2_powers.push(tmp);
            cur_counter+=G2_UNCOMPR_SIZE;
        }

        (g1_powers, g2_powers)
    }
}

// setup algorithm for Baloo
// also includes a bunch of precomputation.
// @max_degree max degree of table polynomial C(X), also the size of the trusted setup
// @N domain size on which proofs are constructed. Should not be smaller than max_degree
// @m lookup size. Can be changed later
// @n = log(N)
#[allow(non_snake_case)]
pub fn setup_lookup(max_degree: &usize, N: &usize, m: &usize, n: &usize) -> PublicParameters
 {

    // Setup algorithm. To be replaced by output of a universal setup before being production ready.
    let mut g1_powers: Vec<G1Affine>=Vec::new();
    let mut g2_powers: Vec<G2Affine>=Vec::new();

    //try opening the file. If it exists load the setup from there, otherwise generate
    let path=format!("srs/srs_{}.setup",max_degree);
    std::fs::create_dir_all("srs").expect("srs directory cannot be created");
    let res = File::open(path.clone());
    let  store_to_file:bool;
    match res{
        Ok(_)=>{
            let now = Instant::now();
            let (_g1_powers, _g2_powers) = PublicParameters::load(&path);
            println!("time to load powers = {:?}", now.elapsed());
            store_to_file = false;
            g1_powers = _g1_powers;
            g2_powers = _g2_powers;
        }
        Err(_)=>{

            // generating powers of g1
            let rng = &mut ark_std::test_rng();
            let beta: Fp256<FrParameters>  = Fr::rand(rng);
            let mut temp = G1Projective::rand(rng).into_affine();

            for _ in 0..(max_degree+1) {
                g1_powers.push( temp.clone() );
                temp = temp.mul( beta ).into_affine();
            }

            // generating powers of g2
            let mut temp = G2Projective::rand(rng).into_affine();
            for _ in 0..(max_degree+1) {
                g2_powers.push( temp.clone() );
                temp = temp.mul( beta ).into_affine();
            }

            store_to_file = true;
        }
    }

    // domain where openings {w_i}_{i in I} are embedded
    let domain_n: GeneralEvaluationDomain<Fr> = GeneralEvaluationDomain::new( n.clone() ).unwrap();
    let domain_N: GeneralEvaluationDomain<Fr> = GeneralEvaluationDomain::new( N.clone() ).unwrap();
    let domain_m: GeneralEvaluationDomain<Fr> = GeneralEvaluationDomain::new( m.clone() ).unwrap();

    // commitment to the vanishing polynomial over domain_N
    let zH: UniPoly381 = domain_N.vanishing_polynomial().into();
    let g1_zH = VariableBaseMSM::multi_scalar_mul(&g1_powers, convert_to_bigints(&zH.coeffs).as_slice()).into_affine();

    let pp = PublicParameters {
        domain_m: domain_m,
        domain_n: domain_n,
        domain_N: domain_N,
        N: N.clone(),
        n: n.clone(),
        m: m.clone(),
        g1_powers: g1_powers.clone(),
        g2_powers: g2_powers.clone(),
        g1_zH: g1_zH.clone(),
    };

     if store_to_file
    {
        pp.store(&path);
    }
    return pp
}


#[allow(non_snake_case)]
#[derive(PartialEq)]
#[derive(Debug)]
//Data structure to be stored in a file: polynomial, its commitment, and its openings (for certain SRS)
pub struct TableInput{
    pub c_poly: DensePolynomial<Fp256<FrParameters>>,
    pub c_com: G1Affine,
    pub c_evals: Vec<Fr>,
    pub openings: Vec<G1Affine>,
    pub zH_openings: Vec<G1Affine>
}


//Compute data to be stored in a file: polynomial, its commitment, and its openings (for certain SRS)
#[allow(non_snake_case)]
impl TableInput{
    fn store(&self, path: &str)
    {
        use std::io::Write;

        //1. Polynomial
        let mut o_bytes = vec![];
        let mut f = File::create(path).expect("Unable to create file");
        let len: u32 = self.c_poly.len().try_into().unwrap();
        let len_bytes = len.to_be_bytes();
        f.write_all(&len_bytes).expect("Unable to write data");
        let len32: usize = len.try_into().unwrap();
        for i in 0..len32
        {
            self.c_poly.coeffs[i].serialize_uncompressed(&mut o_bytes).ok();
        }
        f.write_all(&o_bytes).expect("Unable to write data");

        //2. Commitment
        o_bytes.clear();
        self.c_com.serialize_uncompressed(&mut o_bytes).ok();
        f.write_all(&o_bytes).expect("Unable to write data");

        //3. Evaluations
        o_bytes.clear();
        let len: u32 = self.c_evals.len().try_into().unwrap();
        let len_bytes = len.to_be_bytes();
        f.write_all(&len_bytes).expect("Unable to write data");
        let len32: usize = len.try_into().unwrap();
        for i in 0..len32
        {
            self.c_evals[i].serialize_uncompressed(&mut o_bytes).ok();
        }
        f.write_all(&o_bytes).expect("Unable to write data");

        //4. Openings
        o_bytes.clear();
        let len: u32 = self.openings.len().try_into().unwrap();
        let len_bytes = len.to_be_bytes();
        f.write_all(&len_bytes).expect("Unable to write data");
        let len32: usize = len.try_into().unwrap();
        for i in 0..len32
        {
            self.openings[i].serialize_uncompressed(&mut o_bytes).ok();
        }
        f.write_all(&o_bytes).expect("Unable to write data");

        //5. zH Openings
        o_bytes.clear();
        let len: u32 = self.zH_openings.len().try_into().unwrap();
        let len_bytes = len.to_be_bytes();
        f.write_all(&len_bytes).expect("Unable to write data");
        let len32: usize = len.try_into().unwrap();
        for i in 0..len32
        {
            self.zH_openings[i].serialize_uncompressed(&mut o_bytes).ok();
        }
        f.write_all(&o_bytes).expect("Unable to write data");
    }

    fn load(path: &str) ->TableInput
    {
        const FR_UNCOMPR_SIZE: usize=32;
        const G1_UNCOMPR_SIZE: usize =96;
        let mut data = Vec::new();
        let mut f = File::open(path).expect("Unable to open file");
        f.read_to_end(&mut data).expect("Unable to read data");

        //1. reading  c_poly
        let mut cur_counter:usize  = 0;
        let len_bytes: [u8; 4] = (&data[0..4]).try_into().unwrap();
        let len: u32 = u32::from_be_bytes(len_bytes);
        let mut coeffs = vec![];
        let len32: usize = len.try_into().unwrap();
        cur_counter += 4;
        for i in 0..len32
        {
            let buf_bytes = &data[cur_counter+i*FR_UNCOMPR_SIZE..cur_counter+(i+1)*FR_UNCOMPR_SIZE];
            let tmp = Fr::deserialize_unchecked(buf_bytes).unwrap();
            coeffs.push(tmp);
        }
        cur_counter+=len32*FR_UNCOMPR_SIZE;

        //2. c_com
        let buf_bytes = &data[cur_counter..cur_counter+G1_UNCOMPR_SIZE];
        let c_com  = G1Affine::deserialize_unchecked(buf_bytes).unwrap();
        cur_counter += G1_UNCOMPR_SIZE;

        //3 evaluations
        let len_bytes: [u8; 4] = (&data[cur_counter..cur_counter+4]).try_into().unwrap();
        let len: u32 = u32::from_be_bytes(len_bytes);
        let mut c_evals = vec![];
        let len32: usize = len.try_into().unwrap();
        cur_counter += 4;
        for _ in 0..len32
        {
            let buf_bytes = &data[cur_counter..cur_counter+FR_UNCOMPR_SIZE];
            let tmp = Fr::deserialize_unchecked(buf_bytes).unwrap();
            c_evals.push(tmp);
            cur_counter+=FR_UNCOMPR_SIZE;
        }

        //4 openings
        let len_bytes: [u8; 4] = (&data[cur_counter..cur_counter+4]).try_into().unwrap();
        let len: u32 = u32::from_be_bytes(len_bytes);
        let mut openings = vec![];
        let len32: usize = len.try_into().unwrap();
        cur_counter += 4;
        for _ in 0..len32
        {
            let buf_bytes = &data[cur_counter..cur_counter+G1_UNCOMPR_SIZE];
            let tmp = G1Affine::deserialize_unchecked(buf_bytes).unwrap();
            openings.push(tmp);
            cur_counter+=G1_UNCOMPR_SIZE;
        }

        //5 zH openings
        let len_bytes: [u8; 4] = (&data[cur_counter..cur_counter+4]).try_into().unwrap();
        let len: u32 = u32::from_be_bytes(len_bytes);
        let mut zH_openings = vec![];
        let len32: usize = len.try_into().unwrap();
        cur_counter += 4;
        for _ in 0..len32
        {
            let buf_bytes = &data[cur_counter..cur_counter+G1_UNCOMPR_SIZE];
            let tmp = G1Affine::deserialize_unchecked(buf_bytes).unwrap();
            zH_openings.push(tmp);
            cur_counter+=G1_UNCOMPR_SIZE;
        }

        return TableInput{
            c_poly: DensePolynomial { coeffs },
            c_com: c_com,
            c_evals: c_evals,
            openings: openings,
            zH_openings: zH_openings
        }
    }
}


#[allow(non_snake_case)]
pub fn get_poly_and_g1_openings(
    pp: &PublicParameters,
    actual_degree: usize,
)->TableInput
{

    //try opening the file. If it exists load the setup from there, otherwise generate
    std::fs::create_dir_all("polys").expect("directory cannot be created");

    let path=format!("polys/poly_{}_openings_{}.setup",actual_degree,pp.N);
    let res = File::open(path.clone());
    match res{
        Ok(_)=>{
            println!("file exists");
            let now = Instant::now();
            let table = TableInput::load(&path);
            println!("Time to load openings = {:?}", now.elapsed());
            return table;
        }
        Err(_)=>{
            println!("file does not exist");

            // This randomness should *not* be used for any real world usecases
            let rng = &mut ark_std::test_rng();

            // Commit to a random polynomial
            let c_poly = UniPoly381::rand(actual_degree, rng);

            // Commitment to c(X) in Group 1
            assert!( pp.g1_powers.len() >= c_poly.len(), "Not enough g1 powers for computing [c(x)]_1" );
            let c_com = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&c_poly.coeffs).as_slice()).into_affine();

            // Compute evaluations of C(X) for all omega_i in H
            let c_evals = pp.domain_N.fft( &c_poly );

            // Compute commitments to c(X) - c(omega_i) / (X - omega_i) for all omega_i in H
            let now = Instant::now();
            let openings = multiple_open_g1(&pp.g1_powers[..].into(), &c_poly, pp.n);

            // Compute commitments to zH(X) / (X - omega_i) for all omega_i in H
            let zH: UniPoly381 = pp.domain_N.vanishing_polynomial().into();
            let zH_openings_twice = multiple_open_g1(&pp.g1_powers[..].into(), &zH, pp.n + 1);

            // zH has degree 2^n + 1.
            // multiple_open_g2 returns 2^{n+1} openings
            // Choose the even elements of zH_openings_twice to get required 2^n openings
            let mut zH_openings: Vec<G1Affine> = Vec::new();
            for zH_opening in zH_openings_twice.iter().step_by(2) {
                zH_openings.push( *zH_opening );
            }

            println!("Time to generate openings = {:?}", now.elapsed());
            let table = TableInput{
                c_poly: c_poly,
                c_com: c_com,
                c_evals: c_evals,
                openings: openings,
                zH_openings: zH_openings
            };
            table.store(&path);
            return  table;
        }
    }
}

#[cfg(test)]
pub mod tests{

    use crate::baloo_setup::{PublicParameters,TableInput,setup_lookup,get_poly_and_g1_openings};
    use crate::tools::{UniPoly381,convert_to_bigints};
    use crate::multiopen::multiple_open_g1;

    use ark_bls12_381::{G1Affine,Fr,Bls12_381};
    use std::time::Instant;
    use ark_poly::{EvaluationDomain,GeneralEvaluationDomain};
    use ark_poly_commit::UVPolynomial;
    use ark_ec::{msm::VariableBaseMSM,AffineCurve,ProjectiveCurve,PairingEngine};

    #[allow(non_snake_case)]
    #[test]
    pub fn test_table_input_store_and_load()
    {
        //1. Setup
        let n: usize = 8;
        let N: usize = 1<<n;
        let powers_size: usize = 2*N; //SRS SIZE
        let temp_m = n; //dummy
        let now = Instant::now();
        let pp =setup_lookup(&powers_size,&N,&temp_m,&n);
        let actual_degree = N-1;

        let path=format!("tmp/poly_openings.log");

        std::fs::create_dir_all("tmp").expect("directory cannot be created");


        println!("SRS generated");
        println!("Time    {:?}",  now.elapsed());

        //2. Store
        let rng = &mut ark_std::test_rng();
        let domain: GeneralEvaluationDomain<Fr>  =  EvaluationDomain::new(N).unwrap();
        let c_poly = UniPoly381::rand(actual_degree, rng);
        let c_evals = domain.fft( &c_poly );

        // Commitment to c(X) in Group 1
        assert!( pp.g1_powers.len() >= c_poly.len(), "Not enough g1 powers for computing [c(x)]_1" );
        let c_com = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&c_poly.coeffs).as_slice()).into_affine();


        let now = Instant::now();
        let openings = multiple_open_g1(&pp.g1_powers[..].into(), &c_poly, pp.n);
        println!("Openings 1 generated");
        println!("Time    {:?}",  now.elapsed());

        // Compute commitments to zH(X) / (X - omega_i) for all omega_i in H
        let zH: UniPoly381 = pp.domain_N.vanishing_polynomial().into();
        let now = Instant::now();
        let zH_openings_twice = multiple_open_g1(&pp.g1_powers[..].into(), &zH, pp.n + 1);
        println!("Openings zH generated");
        println!("Time    {:?}",  now.elapsed());

        // zH has degree 2^n + 1.
        // multiple_open_g1 returns 2^{n+1} openings
        // Choose the even elements of zH_openings_twice to get required 2^n openings
        let mut zH_openings: Vec<G1Affine> = Vec::new();
        for zH_opening in zH_openings_twice.iter().step_by(2) {
            zH_openings.push( *zH_opening );
        }
        let table = TableInput{
            c_poly: c_poly,
            c_com: c_com,
            c_evals: c_evals,
            openings: openings,
            zH_openings: zH_openings
        };
        let now = Instant::now();
        table.store(&path);
        println!("Table stored");
        println!("Time    {:?}",  now.elapsed());

        //3. Load
        let table_loaded = TableInput::load(&path);

        //4. Test
        assert_eq!(table,table_loaded);
        //std::fs::remove_file(&path).expect("File can not be deleted");
        std::fs::remove_dir_all("tmp").expect("File can not be deleted")
    }

    #[test]
    #[allow(non_snake_case)]
    pub fn test_public_parameters_store_and_load()
    {
        let n: usize = 4;
        let N: usize = 1<<n;
        let powers_size: usize = 4*N; //SRS SIZE
        let temp_m = n; //dummy
        let pp =setup_lookup(&powers_size,&N,&temp_m,&n);
        let path = "powers.log";
        pp.store(path);
        let loaded = PublicParameters::load(path);
        assert_eq!(pp.g1_powers,loaded.0);
        assert_eq!(pp.g2_powers,loaded.1);
        std::fs::remove_file(&path).expect("File can not be deleted");
    }

    #[test]
    #[allow(non_snake_case)]
    pub fn test_get_poly_and_g1_openings()
    {
        // get some public parameters
        let n: usize = 4;
        let N: usize = 1<<n;
        let powers_size: usize = 4*N; //SRS SIZE
        let temp_m = n; //dummy
        let pp =setup_lookup(&powers_size,&N,&temp_m,&n);

        // run get_poly_and_g1_openings
        let table = get_poly_and_g1_openings(&pp, N-1);

        // Test that zH_openings are correct
        let zH: UniPoly381 = pp.domain_N.vanishing_polynomial().into();
        let g1_zH = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers, convert_to_bigints(&zH.coeffs).as_slice()).into_affine();

        // e( [zH(x)]_1, [1]_2 )
        let pairing1 = Bls12_381::pairing(
               g1_zH.into_projective(),
               pp.g2_powers[0]
        );

        let point = pp.domain_N.element(2);

        // e( H_2 , [x - omega_2 ]_2 )
        let pairing2  =Bls12_381::pairing(
           table.zH_openings[2],
           pp.g2_powers[1].into_projective() -  pp.g2_powers[0].mul(point)
        );

        // check e( [zH(x)]_1, [1]_2 ) = e( H_2 , [x - omega_2 ]_2 )
        assert_eq!(pairing1,pairing2);
    }
}
