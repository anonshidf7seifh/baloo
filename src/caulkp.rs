/*
This file includes the Caulk+'s prover and verifier.
The protocol is described in Figure 1.
*/

use ark_bls12_381::{Bls12_381, G1Affine, G2Affine, Fr};
use ark_ec::{msm::{VariableBaseMSM}, ProjectiveCurve, AffineCurve, PairingEngine};


use crate::baloo_setup::{PublicParameters};
use crate::baloo_lookup::{LookupProverInput};
use crate::tools::{UniPoly381, convert_to_bigints,aggregate_kzg_proofs_g1};

// Input instance structure of caulkp prover and verifier
#[allow(non_snake_case)]
pub struct CaulkpInstance{
    pub m: usize, // size of the subtable
    pub g1_C: G1Affine, // commitment to table C(X)
    pub g1_t: G1Affine, // commitment to subtable t(X) of size m such that t(xi) = C(xi) for all xi in I
    pub g2_zI: G2Affine, // commitment to I, zI(xi) = 0 for all xi in I
}

// Input witness structure of caulkp prover
#[allow(non_snake_case)]
pub struct CaulkpWitness{
    pub set_I: Vec<usize>, // set I of size m
    pub t_poly: UniPoly381, // subtable t(X) of size m such that t(xi) = C(xi) for all xi in I
    pub zI_poly: UniPoly381, // polynomial zI(X) such that zI(xi) = 0 for all xi in I
    pub lagrange_normalisers: Vec< Fr >, // values t(xi)^{-1} for t(X) = zI(X) / (X - xi)
}

/*
Prove knowledge of I, t(X), zI(X) such that:
    1) I subset H, |I| = k
    2) for all xi in I, t(xi) = C(xi)
    3) g1_t =  [t(x)]_1
    4) zI = [zI(x)]_2 for zI(X) = prod_{xi in I}(X - xi)
*/
#[allow(non_snake_case)]
pub fn caulkp_prove(
    pp: &PublicParameters,
    prover_input: &LookupProverInput,
    instance: &CaulkpInstance,
    witness: &CaulkpWitness,
) -> (G1Affine, G1Affine, G1Affine)
    {

    ///////////////////////////////////////////////////////////////////
    //1. Compute W1
    ///////////////////////////////////////////////////////////////////

    // Compute [W1(x)]_1 by aggregating kzg proofs such that
    // W1(X) = (  C(X) - sum_{i in I} c_{i+1} tau_i(X)  ) /  ( prod_{i in I} (X - w^i) )
    let g1_w1 = aggregate_kzg_proofs_g1(&prover_input.openings, &witness.set_I, &witness.lagrange_normalisers);

    ///////////////////////////////////////////////////////////////////
    //2. Compute W2
    ///////////////////////////////////////////////////////////////////

    // Compute [W2(x)]_1 by aggregating zH proofs such that
    // W2(X) = zH(X) / zI(X)
    //       =  (  zH(X) - sum_{i in I} 0 * tau_i(X)  ) /  ( prod_{i in I} (X - w^i) )
    let g1_w2 = aggregate_kzg_proofs_g1(&prover_input.zH_openings, &witness.set_I, &witness.lagrange_normalisers);

    ///////////////////////////////////////////////////////////////////
    //3. Compute W3
    ///////////////////////////////////////////////////////////////////

    // Compute [W3(X)]_1 for W3(X) =  ( zI(X) - X^|I| ) * X^{max_deg - |I| + 1}
    assert!( pp.g1_powers[(pp.g1_powers.len() - instance.m)..].len()
        >= witness.zI_poly.coeffs.len() - 1, "degree problem in prover of caulkp" );
    let g1_w3 = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[
        (pp.g1_powers.len() - instance.m)..],
    &convert_to_bigints( &witness.zI_poly.coeffs[..(witness.zI_poly.coeffs.len() - 1)].into() )).into_affine();

    return (g1_w1, g1_w2, g1_w3)
}


/*
Verify existence of I, t(X), zI(X) such that:
    1) I subset H, |I| = m
    2) for all xi in I, t(xi) = C(xi)
    3) g1_t =  [t(x)]_1
    4) zI = [zI(x)]_2 for zI(X) = prod_{xi in I}(X - xi)
*/
#[allow(non_snake_case)]
#[allow(dead_code)]
pub fn caulkp_verify(
    pp: &PublicParameters,
    instance: &CaulkpInstance,
    g1_w1: &G1Affine,
    g1_w2: &G1Affine,
    g1_w3: &G1Affine
) -> bool
    {

    ///////////////////////////////////////////////////////////////////
    //1. Check e( C - t , [1]_2 ) = e( W1, zI )
    ///////////////////////////////////////////////////////////////////

    // pairing1 = e( C - t , [1]_2)
    let pairing1=Bls12_381::pairing((instance.g1_C.into_projective()-instance.g1_t.into_projective()).into_affine()
    , pp.g2_powers[0]);

    // pairing2 = e( W1, zI )
    let pairing2 = Bls12_381::pairing(g1_w1.clone() , instance.g2_zI );

    assert!(pairing1 == pairing2, "failure on first pairing check of caulkp");

    ///////////////////////////////////////////////////////////////////
    //2. Check e( [zH(x)]_1 , [1]_2 ) = e( W2, zI )
    ///////////////////////////////////////////////////////////////////

    // pairing1 = e( [zH(x)]_1 , [1]_2 )
    let pairing1=Bls12_381::pairing( pp.g1_zH, pp.g2_powers[0]);

    // pairing2 = e( W2, zI )
    let pairing2=Bls12_381::pairing( g1_w2.clone(), instance.g2_zI);

    assert!(pairing1 == pairing2, "failure on second pairing check of caulkp");

    ///////////////////////////////////////////////////////////////////
    //3. Check e( [ x^{N} - k + 1 ]_1 , zI - [ x^m ]_2 ) = e( W3, [1]_2 )
    ///////////////////////////////////////////////////////////////////

    // pairing1 = e( [ x^{N} - m + 1 ]_1 , zI - [ x^m ]_2)
    let pairing1=Bls12_381::pairing(
         pp.g1_powers[ pp.g1_powers.len() - instance.m ],
         (instance.g2_zI.into_projective() - pp.g2_powers[ instance.m ].into_projective()).into_affine() );

    // pairing2 = e( W2, zI )
    let pairing2=Bls12_381::pairing( g1_w3.clone(), pp.g2_powers[0] );

    assert!(pairing1 == pairing2, "failure on third pairing check of caulkp");

    return true;
}

#[cfg(test)]
pub mod tests{

    use crate::baloo_setup::{setup_lookup,get_poly_and_g1_openings};
    use crate::caulkp::{CaulkpInstance,CaulkpWitness,caulkp_prove,caulkp_verify};
    use crate::baloo_lookup::{LookupProverInput};
    use crate::tools::{convert_to_bigints,interpolate,get_lagrange_normalisers,get_vanishing_polynomial};

    use std::time::Instant;
    use rand::Rng;
    use ark_poly::EvaluationDomain;
    use ark_ec::{msm::VariableBaseMSM,ProjectiveCurve};

    #[allow(non_snake_case)]
    #[test]
    pub fn do_multiple_caulkps()
    {
        const MIN_LOG_N: usize  = 7;
        const MAX_LOG_N: usize = 10;
        const EPS: usize=1;
        const MIN_LOG_M: usize=2;
        const MAX_LOG_M: usize=5;

        for n in MIN_LOG_N..=MAX_LOG_N
        {

            //1. Setup
            let N: usize = 1<<n;
            let powers_size: usize = 2*N; //SRS SIZE
            println!("N={}",N);
            let actual_degree = N-EPS;

            for logm in MIN_LOG_M..=std::cmp::min(MAX_LOG_M,n/2-1)
            {
                //3. Setup
                let now = Instant::now();
                let m = 1<<logm;
                let pp = setup_lookup(&powers_size, &N, &m, &n);
                let table = get_poly_and_g1_openings(&pp,actual_degree);
                println!("Time to generate aux domain {:?}", now.elapsed());


                //4. Positions
                let mut rng = rand::thread_rng();
                let mut positions: Vec<usize> = vec![];
                while positions.len() < m {
                    //generate positions randomly in the set
                    let i_j: usize = rng.gen_range(0, actual_degree);
                    if !positions.contains( &i_j ){
                        positions.push(i_j);
                    }
                };
                positions.sort();

                // set_HI contains evaluation points corresponding to positions
                let mut set_HI = vec![];
                for i in 0..positions.len() {
                    set_HI.push( pp.domain_N.element(positions[i]) );
                }

                let (zI_poly, zI_poly_tree) = get_vanishing_polynomial(&set_HI);
                let lagrange_normalisers = get_lagrange_normalisers(&zI_poly, &zI_poly_tree);

                // 5. Commitment to C(X) in Group 1 and zI(X) in Group 2
                assert!( pp.g1_powers.len() >= table.c_poly.len(), "Not enough g1 powers for computing [c(x)]_1" );
                let g1_C = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&table.c_poly.coeffs).as_slice()).into_affine();

                // Commitment to zI(X) in Group 2
                assert!( pp.g2_powers.len() >= zI_poly.len(), "Not enough g2 powers for computing [zI(x)]_2" );
                let g2_zI = VariableBaseMSM::multi_scalar_mul(&pp.g2_powers, convert_to_bigints(&zI_poly.coeffs).as_slice()).into_affine();

                // 6. Compute t(X)
                // t_evals[j] = c_{i_j}
                let mut t_evals = vec![];
                for j in 0..m {
                    t_evals.push( table.c_evals[ positions[j] ] );
                }

                // interpolate t_evals over HI
                let t_poly = interpolate( &t_evals, &zI_poly_tree, &lagrange_normalisers );

                assert!( pp.g1_powers.len() >= t_poly.len(), "Not enough g1 powers for computing [t(x)]_1" );
                let g1_t = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&t_poly.coeffs).as_slice()).into_affine();


                //7. Caulkp inputs
                let prover_input = LookupProverInput{
                    c_poly: table.c_poly.clone(),
                    openings: table.openings.clone(),
                    zH_openings: table.zH_openings.clone()};

                let caulkp_instance = CaulkpInstance {m: m, g1_C: g1_C, g1_t: g1_t, g2_zI: g2_zI};

                let caulkp_witness = CaulkpWitness {set_I: positions.clone(), t_poly: t_poly.clone(), zI_poly: zI_poly.clone(), lagrange_normalisers: lagrange_normalisers.clone()};

                println!("Time to generate inputs = {:?}", now.elapsed());


                let now = Instant::now();
                let (p1,p2,p3) = caulkp_prove(&pp, &prover_input, &caulkp_instance, &caulkp_witness);
                println!("Time to generate proof for = {:?}", now.elapsed());
                let now = Instant::now();
                let res = caulkp_verify(&pp, &caulkp_instance, &p1, &p2, &p3);
                println!("Time to verify proof for  = {:?}",   now.elapsed());
                assert!(res);
                println!("Lookup test succeeded");
            }
        }
    }
}
