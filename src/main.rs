mod baloo_setup;
mod tools;
mod baloo_lookup;
mod multiopen;
mod baloo_transcript;

mod caulkp;

use crate::tools::{read_line,convert_to_bigints};
use crate::baloo_setup::{setup_lookup,get_poly_and_g1_openings};
use crate::baloo_lookup::{LookupProverInput, LookupInstance, LookupWitness,
    compute_lookup_proof, verify_lookup_proof};


use ark_std::{time::Instant};
use ark_poly::{EvaluationDomain, Evaluations as EvaluationsOnDomain};
use ark_ec::{msm::VariableBaseMSM,ProjectiveCurve};
use std::cmp::max;
use rand::Rng;



#[allow(non_snake_case)]
fn main() {

    //1. Setup
    // setting public parameters
    // current kzg setup should be changed with output from a setup ceremony
    println!("What is the bitsize of the degree of the polynomial inside the commitment? ");
    let n: usize = read_line();
    println!("How many positions m do you want to open the polynomial at? ");
    let m: usize = read_line();


    let N: usize = 1 << n;
    let powers_size: usize = max( 2 * N ,  4096 ) ;
    let actual_degree = N - 1;
    let temp_m = n; //dummy

    let now = Instant::now();
    let pp =setup_lookup(&powers_size, &N, &temp_m, &n);
    println!("Time to setup multi openings of table size {:?} = {:?}", actual_degree + 1, now.elapsed());

    //2. Poly and openings
    let now = Instant::now();
    let table = get_poly_and_g1_openings(&pp, actual_degree);
    println!("Time to generate commitment table = {:?}", now.elapsed());

    //3. Positions
    let mut rng = rand::thread_rng();
    let mut positions: Vec<usize> = vec![];
    for _ in 0..m {
        //generate positions randomly in the set
        let i_j: usize = rng.gen_range(0,actual_degree);
        positions.push(i_j);
    };

    //4. generating phi
    let mut phi_evals = vec![];
    for j in 0..m {
        phi_evals.push( table.c_evals[ positions[j] ] );
    }
    for _ in m..pp.domain_m.size() {
        phi_evals.push( table.c_evals[ 0 ] );

        // also add 0 to positions
        positions.push(0);
    }

    let phi_poly = EvaluationsOnDomain::from_vec_and_domain(phi_evals.clone(), pp.domain_m).interpolate();


    //5. Running proofs
    let now = Instant::now();

    // Commitment to C(X) in Group 1
    assert!( pp.g1_powers.len() >= table.c_poly.len(), "Not enough g1 powers for computing [c(x)]_1" );
    let g1_C = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&table.c_poly.coeffs).as_slice()).into_affine();

    // Commitment to phi(X) in Group 1
    assert!( pp.g1_powers.len() >= phi_poly.len(), "Not enough g1 powers for computing [phi(x)]_1" );
    let g1_phi = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&phi_poly.coeffs).as_slice()).into_affine();

    println!("Time to generate inputs = {:?}", now.elapsed());

    let lookup_instance = LookupInstance{
        m: pp.domain_m.size(),
        g1_C: g1_C.clone(),
        g1_phi: g1_phi.clone(),
    };

    let lookup_witness = LookupWitness{
        c_poly: table.c_poly.clone(),
        c_evals: table.c_evals.clone(),
        phi_poly: phi_poly,
        positions: positions,
    };

    let prover_input = LookupProverInput{
        c_poly: table.c_poly.clone(),
        openings: table.openings.clone(),
        zH_openings: table.zH_openings.clone()};



    println!("We are now ready to run the prover.  How many times should we run it?" );
    let number_of_openings: usize = read_line();
    let now = Instant::now();
    let lookup_proof = compute_lookup_proof(&pp, &prover_input, &lookup_instance, &lookup_witness );
    for _ in 1..number_of_openings {
        _ = compute_lookup_proof(&pp, &prover_input, &lookup_instance, &lookup_witness );
    }
    println!("Time to evaluate {} times {} multi-openings of table size {:?} = {:?} ", number_of_openings, m, N, now.elapsed());

    let now = Instant::now();
    for _ in 0..number_of_openings {
        verify_lookup_proof(&pp, &lookup_instance, &lookup_proof);
    }
    println!("Time to verify {} times {} multi-openings of table size {:?} = {:?} ", number_of_openings, m, N, now.elapsed());


    assert!(verify_lookup_proof(&pp, &lookup_instance, &lookup_proof), "Result does not verify");

    }
