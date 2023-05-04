/*
This file includes backend tools:
(1) read_line() is for taking inputs from the user
(2) convert_to_bigints is for formatting inputs into multiscalar operations
(3) aggregate_kzg_proofs_g1 is for aggregating KZG polynomial commitments in G1
(4) get_vanishing_polynomial is for computing the vanishing polynomial over any set of points I
(5) compute_evaluations is for computing f(X) over the set I that we have previously computed the vanishing polynomial for.
(6) get_lagrange_normalisers is a precomputation for interpolating over set I
(8) interpolate takes a set of evaluations over set I and returns a polynomial f(X) that corresponds to these evaluations.
(9) fast_divide_with_q_and_r takes in p(X), g(X) and computes q(X), r(X) such that p(X) = g(X) q(X) + r(X)
*/

use ark_bls12_381::{Bls12_381, FrParameters, G1Affine, G1Projective, Fr};
use ark_ff::{PrimeField, Fp256, batch_inversion};
use ark_std::{One};
use ark_poly::{univariate::{DensePolynomial}, UVPolynomial, Polynomial};
use ark_ec::{PairingEngine, ProjectiveCurve, AffineCurve};
use ark_std::Zero;

use std::{io, str::FromStr, error::Error, ops::{Div}, vec};

pub type UniPoly381 = DensePolynomial<<Bls12_381 as PairingEngine>::Fr>;


// Function for reading inputs from the command line.
pub fn read_line<T: FromStr>() -> T
where <T as FromStr>::Err: Error + 'static
{
    let mut input = String::new();
    io::stdin().read_line(&mut input).expect("Failed to get console input.");
    let output: T = input.trim().parse().expect("Console input is invalid.");
    output
}


//copied from arkworks
pub fn convert_to_bigints<F: PrimeField>(p: &Vec<F>) -> Vec<F::BigInt> {
    let coeffs = ark_std::cfg_iter!(p)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>();
    coeffs
}

//////////////////////////////////////////////////////

/*
Algorithm for aggregating KZG proofs into a single proof
Described in Section 4.6.3 Subset openings of Caulk
compute Q =\sum_{j=1}^m \frac{Q_{i_j}}}{\prod_{1\leq k\leq m,\; k\neq j}(\omega^{i_j}-\omega^{i_k})}
*/
pub fn aggregate_kzg_proofs_g1(
    openings: &Vec<G1Affine>,  //Q_i
    positions: &Vec<usize>,    //i_j
    lagrange_normalisers: &Vec<Fr>
)->G1Affine
{
    let mut res = G1Projective::zero();

    for j in 0..positions.len()
    {
        res = res + openings[ positions[j] ].mul( lagrange_normalisers[j] );
    }
    return res.into_affine();
}


// Given [f_1(X), ... , f_{2d}(X)] returns [ f_1(X) * f_{d+1}(X), ... , f_d(X) * f_{2d}(X) ]
// runs in d ( n log(n) ) time for n the degree of f_i(X)
#[allow(non_snake_case)]
fn get_vanishing_polynomial_recurse(
    vec_polys: Vec< DensePolynomial<Fp256<FrParameters>> >
) -> Vec< DensePolynomial<Fp256<FrParameters>> >
{
    let mut vec_polys_new = vec![];

    // m  =  d / 2
    let m = vec_polys.len().div(2);


    for i in 0..m {
        if vec_polys.len() > (2 * i + 1) {
            vec_polys_new.push( &vec_polys[ 2 * i] * &vec_polys[2 * i + 1] );
        }
        else if vec_polys.len() > (2 * i) {
            vec_polys_new.push( vec_polys[ 2 * i].clone()  );
        }
        else {
            vec_polys_new.push( DensePolynomial::from_coefficients_slice( &[ Fr::one() ] ) );
        }
    }
    return vec_polys_new
}

// Computes zI(X) = prod_{xi in I}(X - xi) for H_I not necessarily a set of roots of unity.
// Also stores the subtree for evaluating polynomials over domain I quickly
// runs in |I| log^2(|I|) time
// |set_I| must be a power of two, else result will not be valid.
#[allow(non_snake_case)]
pub fn get_vanishing_polynomial(
    set_I: &Vec<Fr>
) -> (DensePolynomial<Fp256<FrParameters>>, Vec< Vec<DensePolynomial<Fp256<FrParameters>>> >)
{

    // check set_I has valid length
    let length_set_I: i32 = set_I.len().try_into().unwrap();
    assert!( length_set_I & (length_set_I - 1) == 0, "Inputs to get_vanishing_polynomial() not a power of 2");

    let mut vanishing_tree = vec![];

    // polys_I = [ (X - xi_1), (X - xi_2), ... , (X - xi_|I|) ]
    let mut polys_I = vec![];
    for i in 0..set_I.len() {
        polys_I.push( DensePolynomial::from_coefficients_slice( &[ -set_I[i].clone(), Fr::one() ]) )
    };

    vanishing_tree.push( polys_I.clone() );

    // loop of length log(|I|)
    // Given [f_1(X), ... , f_{2d}(X)] each iter returns [ f_1(X) * f_{d+1}(X), ... , f_d(X) * f_{2d}(X) ]
    while polys_I.len() > 1 {
        polys_I = get_vanishing_polynomial_recurse(polys_I);
        vanishing_tree.push( polys_I.clone() );
    }

    return (polys_I[0].clone(), vanishing_tree)
}

// takes as input a polynomial f(X) and the tree of a vanishing polynomial of some set H_I
// the tree is as an auxiliary output of the get_vanishing_polynomial() function for H_I
// outputs evals such that for xi_j in H_I, we have evals[j] = f(xi_j)

// runs in time m log^2(m)
// See algorithm 10.5 of Joachim von zur Gathen and Jurgen Gerhard, Modern Computer Algebra, Third Edition
#[allow(non_snake_case)]
pub fn compute_evaluations(
    polynomial: &DensePolynomial< Fp256<FrParameters> >,
    vanishing_tree: &Vec< Vec<DensePolynomial<Fp256<FrParameters>>> >)
    -> Vec< Fr >
{

    // start with [ f(X) ]
    let mut current_entry: Vec< DensePolynomial<Fp256<FrParameters>>> = Vec::new();
    current_entry.push( polynomial.clone() );

    // for [f1(X), f2(X)] outputs [f1(X) mod tree_{i,1}(X),f2(X) mod tree_{i,2}(X), f2(X) mod tree_{i,1}(X), f2(X) mod tree_{i,2}(X)]
    // stops when [f1(X), ... , fn(X)] all have degree 0
    let mut i: usize = vanishing_tree.len() - 1;
    while current_entry[0].degree() > 0 {
        i-=1;
        current_entry = compute_evaluations_recurse(current_entry, &vanishing_tree[i]);
    }

    // put current_entry in field element form
    let mut evals = vec![];
    for j in 0..current_entry.len() {

        // prevents error if fj(X) mod tree_{i,b}(X) = 0 at some point,
        if current_entry[j]!= DensePolynomial::from_coefficients_slice( &[ Fr::zero() ] ) {
            evals.push( current_entry[j][0] );
        }
        else {
            evals.push(Fr::zero());
        }
    }

    return evals
}

#[allow(non_snake_case)]
//for [f1(X), f2(X)] outputs [f1(X) mod tree_{i,1}(X),f2(X) mod tree_{i,2}(X), f2(X) mod tree_{i,1}(X), f2(X) mod tree_{i,2}(X)]
fn compute_evaluations_recurse(
    current_entry: Vec< DensePolynomial<Fp256<FrParameters>> > ,
    tree_entry: &Vec< DensePolynomial<Fp256<FrParameters>> >
) -> Vec< DensePolynomial<Fp256<FrParameters>> >
{
    let mut new_entry = vec![];

    for i in 0..current_entry.len() {
        let ( _ , f_mod_tree_i1 ) = fast_divide_with_q_and_r( &current_entry[i], &tree_entry[2*i]).unwrap();
        let ( _ , f_mod_tree_i2 ) = fast_divide_with_q_and_r( &current_entry[i], &tree_entry[2*i + 1]).unwrap();
        new_entry.push( f_mod_tree_i1  );
        new_entry.push( f_mod_tree_i2  );
    }

    return new_entry
}

// Compute (a1, ... , an) such that tau_i(X) = a_i ( zI(X) / (X - xi_i) ) are the lagrange polynomials for H_I
// Here zI(X) = prod_{xi_i in H_I}( X - xi_i)
// the tree is as an auxiliary output of the get_vanishing_polynomial() function for H_I
// Uses that a_i = zI'( xi_i) for zI'(X) the derivative of zI(X)
// Runs in time m log^2(m)
pub fn get_lagrange_normalisers(
    vanishing_polynomial: &DensePolynomial<Fp256<FrParameters>>,
    vanishing_polynomial_tree: &Vec< Vec<DensePolynomial<Fp256<FrParameters>>> >
) -> Vec<Fr>
{

    // differentiate zI(X) to get zI'(X)
    let derivative_poly = differentiate( vanishing_polynomial );

    // compute zI'(X) over I
    let mut evals = compute_evaluations( &derivative_poly, vanishing_polynomial_tree);

    // find inverses of [zI'(xi_1), ... zI'(xi_n)]
    batch_inversion( &mut evals );

    return evals
}

// differentiate f(X) = sum_i a_i X^i
// returns f'(X) = sum_i i a_i X^{i - 1}
fn differentiate( polynomial: &DensePolynomial<Fp256<FrParameters>> )
-> DensePolynomial<Fp256<FrParameters>> {

    let mut derivative_vec = vec![];

    let mut power = Fr::one();

    for i in 1..polynomial.len() {
        derivative_vec.push( power * &polynomial[i] );
        power = power + Fr::one();
    }

    return DensePolynomial::from_coefficients_slice( &derivative_vec.as_slice() );
}


// takes as input evals such that for xi_j in H_I, we have evals[j] = f(xi_j)
// the tree is as an auxiliary output of the get_vanishing_polynomial() function for H_I
// the lagrange_normalisers are outputs of the get_lagrange_normalisers() function for zI(X)
// outputs polynomial f(X)

// runs in time m log^2(m)
// See algorithm 10.11 of Joachim von zur Gathen and Jurgen Gerhard, Modern Computer Algebra, Third Edition
#[allow(non_snake_case)]
pub fn interpolate(
    evals: &Vec<Fr>,
    vanishing_tree: &Vec< Vec<DensePolynomial<Fp256<FrParameters>>> >,
    lagrange_normalisers: &Vec<Fr> )
    -> DensePolynomial<Fp256<FrParameters>>
{

    // start with Hadamard product of evals with lagrange_normalisers
    let mut scaled_evals: Vec<Fr>  = Vec::new();
    for i in 0..evals.len() {
        scaled_evals.push(  evals[i] * lagrange_normalisers[i] );
    }

    return interpolate_recurse( &scaled_evals, vanishing_tree )
}

// runs in time m log^2(m)
// See algorithm 10.9 of Joachim von zur Gathen and Jurgen Gerhard, Modern Computer Algebra, Third Edition
#[allow(non_snake_case)]
fn interpolate_recurse(
    evals: &Vec<Fr>,
    vanishing_tree: &Vec< Vec<DensePolynomial<Fp256<FrParameters>>> >
    )
    -> DensePolynomial<Fp256<FrParameters>>
{
    if evals.len() == 1 {
        return DensePolynomial::from_coefficients_slice( &[ evals[0] ])
    }

    else {
        let mut vanishing_tree0: Vec< Vec<DensePolynomial<Fp256<FrParameters>>> > = Vec::new();
        let mut vanishing_tree1: Vec< Vec<DensePolynomial<Fp256<FrParameters>>> > = Vec::new();
        let len_tree = vanishing_tree.len();

        for i in 0..(len_tree - 1) {
            let m = vanishing_tree[i].len().div(2);
            vanishing_tree0.push( vanishing_tree[i][..m].to_vec() );
            vanishing_tree1.push( vanishing_tree[i][m..].to_vec() )
        }

        let n = evals.len().div(2);
        let r0_poly = interpolate_recurse( &evals[..n].to_vec(),  &vanishing_tree0 );
        let r1_poly = interpolate_recurse( &evals[n..].to_vec(),  &vanishing_tree1 );

        let m0_poly:DensePolynomial<Fp256<FrParameters>> = vanishing_tree[ len_tree - 2][1].clone().into();
        let m1_poly:DensePolynomial<Fp256<FrParameters>> = vanishing_tree[ len_tree - 2][0].clone().into();

        return &r0_poly * &m0_poly  + &r1_poly * &m1_poly
    }


}

#[allow(non_snake_case)]
//for [f(X),l] outputs [g(X)] such that f(X)* g(X)= 1 mod X^l
fn poly_inverse(
    poly: &DensePolynomial<Fp256<FrParameters>>,
    l: u32
)-> Option<DensePolynomial<Fp256<FrParameters>>>
{
    if poly.is_zero() {
        panic!("Dividing by zero polynomial")
    }
    else{
        let mut g = DensePolynomial::from_coefficients_slice(&[ Fr::one()/poly.coeffs[0]]); //g0=f(0)
        let mut i=1;
        let two  = Fr::from_str("2").unwrap();
        while (1<<i)<2*l{ //i ranges from 1 to ceiling (log_2 l)
            let tmp = (&g*two)+&(poly * &(&g * &g))*(-Fr::one()); //g_{i+1} = (2g_i - f g_i^2)\bmod{x^{2^{i+1}}}
            let mut a = tmp.coeffs().to_vec();
            a.resize(1<<i, Fr::zero()); //mod x^(2^i)
            g = DensePolynomial::from_coefficients_vec(
                a
            );
            i=i+1;

        }
        Some(g)
    }
}

fn poly_reverse(
    poly: &DensePolynomial<Fp256<FrParameters>>
)->DensePolynomial<Fp256<FrParameters>>
{
    let vec_coeff = poly.coeffs().to_vec();

    let mut x = vec![];
    x.resize(poly.degree()+1, Fr::one());
    for i in 0..poly.degree()+1
    {
        x[i] = vec_coeff[poly.degree()-i];
    }
    let out = DensePolynomial::from_coefficients_vec(x);
    out
}

//for p(X)  outputs p(X) mod X^l
fn poly_trim(
    poly: &DensePolynomial<Fp256<FrParameters>>,
    l: usize
)
->DensePolynomial<Fp256<FrParameters>>
{
    let mut vec_coeff =  poly.coeffs().to_vec();
    vec_coeff.resize(l, Fr::zero());
    return DensePolynomial::from_coefficients_vec(vec_coeff);
}


#[allow(non_snake_case)]
//for [p(X), g(X)] outputs [q(X),r(X)] such that p(X) = g(X)q(X)+r(X)
pub fn fast_divide_with_q_and_r(
    poly: &DensePolynomial<Fp256<FrParameters>>,
    divisor: &DensePolynomial<Fp256<FrParameters>>,
) -> Option<(DensePolynomial<Fp256<FrParameters>>, DensePolynomial<Fp256<FrParameters>>)> {
    if poly.is_zero() {
        Some((DensePolynomial::zero(), DensePolynomial::zero()))
    } else if divisor.is_zero() {
        panic!("Dividing by zero polynomial")
    } else if poly.degree() < divisor.degree() {
        Some((DensePolynomial::zero(), poly.clone().into()))
    } else {
        // Now we know that self.degree() >= divisor.degree();
        // Use the formula for q: rev(q)=  rev(f)* rev(g)^{-1} mod x^{deg(f)-deg(g)+1}.
        let rev_f =  poly_reverse(poly); //reverse of f
        let rev_g = poly_reverse(divisor); //reverse of g
        let inv_rev_g = poly_inverse(&rev_g,poly.degree() as u32+1).unwrap();
        let tmp = &rev_f*&inv_rev_g;
        let rev_q = poly_trim(&tmp,poly.degree()-divisor.degree()+1);
        let quotient = poly_reverse(&rev_q);
        let remainder = poly + &(&(&quotient * divisor)*(-Fr::one()));

        Some((quotient, remainder))
    }
}



//////////////////////////////////////////////////////

#[cfg(test)]
pub mod tests {


    use crate::tools::{UniPoly381, poly_reverse};
    use crate::baloo_setup::{setup_lookup};

    use ark_poly::{univariate::DensePolynomial as DensePoly,univariate::DenseOrSparsePolynomial, UVPolynomial, Polynomial};
    use ark_ec::{msm::VariableBaseMSM, AffineCurve, ProjectiveCurve,PairingEngine};
    use std::time::{Instant};
    use ark_bls12_381::{Bls12_381,Fr};
    use ark_std::{UniformRand, One, Zero};

    use super::{poly_inverse, poly_trim,fast_divide_with_q_and_r,get_vanishing_polynomial,
                compute_evaluations,get_lagrange_normalisers,interpolate, convert_to_bigints,
                aggregate_kzg_proofs_g1};

    #[allow(non_snake_case)]
    #[test]
    pub fn test_aggregated_kzg(){

        //1. Setup
        let n = 7;
        let N: usize = 1<<n;
        let powers_size: usize = 2*N;
        let pp =setup_lookup(&powers_size,&N,&n.clone(),&n);

        let rng = &mut ark_std::test_rng();
        let poly = UniPoly381::rand(23, rng);


        let set_I = [ Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)].to_vec();
        let ( zI_poly , zI_poly_tree ) = get_vanishing_polynomial(&set_I);
        let lagrange_normalisers = get_lagrange_normalisers( &zI_poly, &zI_poly_tree );

        assert!( pp.g1_powers.len() >= poly.len(), "Not enough g1 powers for computing [poly(x)]_1" );
        let g1_poly = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&poly.coeffs).as_slice()).into_affine();

        // compute KZG opening proofs for all xi in set_I
        let mut openings = vec![];
        for xi in set_I {

            // compute kzg proof
            let mut numerator = poly.clone();
            numerator[0] = numerator[0] - poly.evaluate( &xi );
            let denominator = DensePoly::from_coefficients_vec( vec![ -xi, Fr::one() ] );
            let quotient = &numerator / &denominator ;

            // check quotient okay
            assert_eq!( numerator, &denominator * &quotient );

            assert!( pp.g1_powers.len() >= quotient.len(), "Not enough g1 powers for computing [poly(x)]_1" );
            let kzg_proof = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&quotient.coeffs).as_slice()).into_affine();

            // quick check that kzg_proof is okay
            let g1_eval_xi = pp.g1_powers[0].mul( poly.evaluate( &xi ) );
            let pairing1=Bls12_381::pairing((g1_poly.into_projective() - &g1_eval_xi ).into_affine()
            , pp.g2_powers[0]);

            let pairing2 = Bls12_381::pairing( kzg_proof.clone() , ( pp.g2_powers[1].into_projective()
            - pp.g2_powers[0].mul(  xi.clone() ) ).into_affine() );

            assert_eq!(pairing1, pairing2);
            openings.push( kzg_proof );
        }


        let pi_agg = aggregate_kzg_proofs_g1( &openings, &[0,1,2,3].to_vec(), &lagrange_normalisers);

        // Compute t(X) such that t( xi ) = poly( xi ) for xi in set_I
        let t_evals = compute_evaluations( &poly, &zI_poly_tree );
        let t_poly = interpolate( &t_evals, &zI_poly_tree, &lagrange_normalisers );

        assert!( pp.g1_powers.len() >= t_poly.len(), "Not enough g1 powers for computing [t(x)]_1" );
        let g1_t = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&t_poly.coeffs).as_slice()).into_affine();

        assert!( pp.g2_powers.len() >= zI_poly.len(), "Not enough g2 powers for computing [zI(x)]_1" );
        let g2_zI = VariableBaseMSM::multi_scalar_mul(&pp.g2_powers[..], convert_to_bigints(&zI_poly.coeffs).as_slice()).into_affine();

        let pairing1=Bls12_381::pairing((g1_poly.into_projective() - &g1_t.into_projective() ).into_affine()
        , pp.g2_powers[0]);

        let pairing2 = Bls12_381::pairing( pi_agg , g2_zI );

        assert_eq!(pairing1, pairing2);
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_vanishing_polynomial(){

        let rng = &mut ark_std::test_rng();

        let set_I = [ Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)].to_vec();
        let (zI_poly, _ ) = get_vanishing_polynomial(&set_I);

        let mut zI_naive = DensePoly::from_coefficients_vec( vec![ Fr::one() ] );

        for i in 0..set_I.len() {
            let temp = DensePoly::from_coefficients_vec( vec![ -set_I[i], Fr::one() ] );
            zI_naive = &zI_naive * &temp;
        };

        assert_eq!(zI_poly,zI_naive);
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_evaluations(){

        let rng = &mut ark_std::test_rng();

        let poly = UniPoly381::rand(23, rng);

        let set_I = [ Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)].to_vec();
        let ( _ , zI_poly_tree) = get_vanishing_polynomial(&set_I);

        let evals = compute_evaluations( &poly, &zI_poly_tree );

        let mut evals_naive: Vec<Fr> = Vec::new();

        for i in 0..set_I.len() {
            evals_naive.push( poly.evaluate( &set_I[i] ) )
        };

        assert_eq!(evals, evals_naive);
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_lagrange_normalisers(){

        let rng = &mut ark_std::test_rng();

        let set_I = [ Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)].to_vec();
        let ( zI_poly , zI_poly_tree) = get_vanishing_polynomial(&set_I);

        let lagrange_normalisers = get_lagrange_normalisers(&zI_poly, &zI_poly_tree);

        for i in 0..set_I.len() {
            let mut lagrange_poly = &zI_poly * lagrange_normalisers[i];
            lagrange_poly = &lagrange_poly / &DensePoly::from_coefficients_vec( vec![ -set_I[i], Fr::one() ] );

            for j in 0..set_I.len() {
                if j == i {
                    assert_eq!( lagrange_poly.evaluate( &set_I[i] ), Fr::one() );
                }
                else {
                    assert_eq!( lagrange_poly.evaluate( &set_I[j] ), Fr::zero() );
                }
            }
        }
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_interpolate() {
        let rng = &mut ark_std::test_rng();
        let poly = UniPoly381::rand(23, rng);

        let mut set_I = vec![];
        for _ in 0..32 {
            set_I.push( Fr::rand(rng) );
        }

        let ( zI_poly , zI_poly_tree) = get_vanishing_polynomial(&set_I);

        let evals = compute_evaluations( &poly, &zI_poly_tree );

        let lagrange_normalisers = get_lagrange_normalisers(&zI_poly, &zI_poly_tree);

        let poly2 = interpolate(&evals, &zI_poly_tree, &lagrange_normalisers);

        assert_eq!(poly, poly2);

    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_poly_inverse(){
        let max_m: u32=20;
        let rng = &mut ark_std::test_rng();
        let poly_one = DensePoly::from_coefficients_vec(vec![Fr::one()]);

        for i in 1..max_m{
            println!("inverse of degree {:?}", i);
            let c_poly = UniPoly381::rand(i as usize, rng);
            for l in i+1..max_m{
              let inv = poly_inverse(&c_poly, l).unwrap();
              let prod = &c_poly * &inv;
              let res = poly_trim(&prod, l as usize);
              assert_eq!(poly_one,res);
            }
        }
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_poly_reverse(){
        let max_m: u32=20;
        let rng = &mut ark_std::test_rng();
        let c_poly = UniPoly381::rand(max_m as usize, rng);
        let rev = poly_reverse(&c_poly);
        let res = poly_reverse(&rev);
        assert_eq!(res,c_poly)
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_fast_poly_division(){
        let max_m: u32=20;
        let rng = &mut ark_std::test_rng();

        for i in 2..max_m{
            println!("division of degree {:?}", i);
            let c_poly = UniPoly381::rand(i as usize, rng);
            let g_poly= UniPoly381::rand((i>>1) as usize, rng);
            let (q,r) = fast_divide_with_q_and_r(&c_poly,&g_poly).unwrap();
            let res = (&q* &g_poly)+r.clone();
            assert_eq!(c_poly,res);
            assert!(r.degree() < g_poly.degree());
        }
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn compare_fast_poly_division(){
        let max_m: u32=10;
        let rng = &mut ark_std::test_rng();

        for j in 1..max_m{
            let i = 1<<j;
            println!("division of degree {:?}", i);
            let c_poly = UniPoly381::rand(i as usize, rng);
            let c_poly_sp = DenseOrSparsePolynomial::from( c_poly.clone() );
            let g_poly= UniPoly381::rand((i>>1) as usize, rng);
            let g_poly_sp = DenseOrSparsePolynomial::from( g_poly.clone() );
            let now = Instant::now();
            let (q,r) = fast_divide_with_q_and_r(&c_poly,&g_poly).unwrap();
            println!("Time to fast divide   {:?}",  now.elapsed());
            let _now2 = Instant::now();
            let (_q2,_r2) = c_poly_sp.divide_with_q_and_r(&g_poly_sp).unwrap();
            println!("Time to regular divide   {:?}",  now.elapsed());
            let res = (&q* &g_poly)+r;
            assert_eq!(c_poly,res);

        }
    }


}
