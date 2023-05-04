/*
This file includes the Baloo prover and verifier.
The protocol is described in Figure 5 and 6.
*/

use ark_bls12_381::{Bls12_381,Fr,FrParameters,G1Affine, G2Affine};
use ark_poly::{univariate::DensePolynomial, Evaluations as EvaluationsOnDomain};
use ark_ff::{Fp256, Field,batch_inversion};

use ark_poly::{EvaluationDomain, UVPolynomial, Polynomial};
use ark_ec::{AffineCurve,ProjectiveCurve,PairingEngine, msm::VariableBaseMSM};

use ark_std::{One, Zero};

use std::time::{Instant};
use std::vec::Vec;


use crate::baloo_setup::{PublicParameters};

use crate::caulkp::{CaulkpInstance, CaulkpWitness, caulkp_prove};
use crate::baloo_transcript::{BalooTranscript, BalooSafeTranscript, SigmaPattern,SigmaOp};
use crate::tools::{UniPoly381,
    convert_to_bigints,
    get_vanishing_polynomial, get_lagrange_normalisers, interpolate,
    fast_divide_with_q_and_r};

// Input instance structure of lookup prover and verifier
#[allow(non_snake_case)]
pub struct LookupInstance{
    pub m: usize, // degree of phi(X)
    pub g1_C: G1Affine,   //polynomial C(X) that represents a table
    pub g1_phi: G1Affine,  //polynomial phi(X) that represents the values to look up
}

// Input witness structure of lookup prover
#[allow(non_snake_case)]
pub struct LookupWitness{
    pub c_poly: DensePolynomial<Fp256<FrParameters>>,   //polynomial C(X) that represents a table
    pub phi_poly: DensePolynomial<Fp256<FrParameters>>,  //polynomial phi(X) that represents the values to look up
    pub positions: Vec<usize>,    // positions where we open C(X)
    pub c_evals: Vec<Fr>,    // evaluations of C(X) over the positions.
}

// Auxilliary precomputed information to speed up prover
#[allow(non_snake_case)]
pub struct LookupProverInput{
    pub c_poly: DensePolynomial<Fp256<FrParameters>>,   //polynomial C(X) that represents a table
    pub openings: Vec<G1Affine>, // precomputed opening proofs of C(X) at all points w in H
    pub zH_openings: Vec<G1Affine>, // precomputed opening proofs of zH(X) at all points w in H
}

//Lookup proof data structure
#[allow(non_snake_case)]
pub struct LookupProof{
    // pi1 from step4
    pub g1_v: G1Affine,
    pub g2_zI: G2Affine,
    pub g1_t: G1Affine,
    // pi2 from step 8
    pub g1_D: G1Affine,
    pub g1_R: G1Affine,
    pub g1_Q2: G1Affine,
    // pi3 from step 11
    pub g1_E: G1Affine,
    pub g1_Q1: G1Affine,
    // pi4 from step 18
    pub u1: Fr,
    pub u2: Fr,
    pub u3: Fr,
    pub u4: Fr,
    pub u5: Fr,
    pub g1_a: G1Affine,
    pub g1_w1: G1Affine,
    pub g1_w2: G1Affine,
    pub g1_w3: G1Affine,
    pub g1_w4: G1Affine,
}



//The Baloo lookup prover as described in Figure 5.
#[allow(non_snake_case)]
pub fn compute_lookup_proof(
    pp: &PublicParameters,
    input: &LookupProverInput,
    instance: &LookupInstance,
    witness: &LookupWitness,
)  -> LookupProof
{

    ///////////////////////////////////////////////////////////////////
    //1. Parse inputs
    ///////////////////////////////////////////////////////////////////
    let m = instance.m.clone();
    let z_Vm: UniPoly381 = pp.domain_m.vanishing_polynomial().into();
    let d = pp.g1_powers.len() - 1;

    /*let mut transcript = BalooTranscript::new();
    transcript.append_element(b"m", &m);
    transcript.append_element(b"g1_C", &instance.g1_C);
    transcript.append_element(b"g1_phi", &instance.g1_phi);*/

    
    ///////////////////////////////////////////////////////////////////
    //1.1 Safe transcript initialization
    ///////////////////////////////////////////////////////////////////
    use crate:: baloo_transcript::{SigmaPattern,SigmaOp,BalooSafeTranscript};
    use neptune::sponge::vanilla::{Sponge,SpongeTrait,Mode};
    use neptune::{Strength}; 
    use blstrs::Scalar as FrBlst; 
    use generic_array::typenum;
    let pattern = SigmaPattern(vec![
        SigmaOp::SendF(1),
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::SendG2(1),
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::ReceiveF(1),//alpha
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::ReceiveF(1),//beta
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::ReceiveF(1),//rho
        SigmaOp::ReceiveF(1),//gamma
        SigmaOp::ReceiveF(1),//delta
    ]);
    let p = Sponge::<FrBlst, typenum::U3>::api_constants(Strength::Standard);
    let mut safe_transcript = BalooSafeTranscript::<Fr,FrBlst>::new_with_constants(&pattern, &p);
    safe_transcript.add_field_element(&Fr::from(m as i128));
    safe_transcript.add_G1_element(&instance.g1_C);
    safe_transcript.add_G1_element(&instance.g1_phi);


    ///////////////////////////////////////////////////////////////////
    //2. Choose the set I, i.e. the set of positions in the subtable
    ///////////////////////////////////////////////////////////////////

    let start_step_2 = Instant::now();
    // set_I includes each position only once.
    let mut set_I: Vec<usize> = Vec::new();
    //set_I.resize( m, 1 );

    let mut k:usize = 0; 
    for j in 0..m {
        let i_j = witness.positions[j].clone();

        // if positions[i] is not repeated then include.
        if !set_I.contains( &i_j )  {
            set_I.push( i_j );
        }

        // if positions[i] is repeated, pad with a value not in positions.
        else {
            while set_I.contains( &k ) {  k += 1;  }
            set_I.push( k ) ;
        }
    }
    set_I.sort();

    // phi(nu_j) =   t( xi_{ col(j) } ) where xi_{col(j)} = h_{i_{col(j)}}
    let mut col = Vec::new();
    for i in 0..m {

        for j in 0..m {
            if set_I[j] == witness.positions[i] {
                col.push( j );
            }
        }
    }

    println!("col.len() = {:?}, m = {:?}", col.len(), m);

    // set_HI contains evaluation points corresponding to set_I positions
    let mut set_HI = vec![];
    for i in 0..set_I.len() {
        set_HI.push( pp.domain_N.element(set_I[i]) );
    }

    println!("Time for lookup step 2 = {:?}", start_step_2.elapsed());


    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 3. Compute v(X) = sum_{j=1}^m h_{i_col(j)}^{-1} mu_j(X)
    //////////////////////////////////////////////////////////////////////////////////////////////////////////

    let start_step_3 = Instant::now();

    // phi(nu_j) =   t( xi_{ col(j) } ) where xi_{col(j)} = h_{i_{col(j)}}
    let mut v_vals= vec![];
    for j in 0..m {
        assert!( col.len() > j , "assertion fails for col" );
        assert!( set_I.len() > col[j] , "assertion fails for set_I" );
        assert!( pp.domain_N.size() > set_I[ col[j] ] , "assertion fails for domain_N" );
        v_vals.push( pp.domain_N.element( set_I[ col[j] ] ).inverse().unwrap() );
    }

    let v_poly = EvaluationsOnDomain::from_vec_and_domain(v_vals.clone(), pp.domain_m).interpolate();
    println!("Time for lookup step 3 = {:?}", start_step_3.elapsed());

    ///////////////////////////////////////////////////////////////////
    //4. Compute * zI(X) =  prod_{i in I} (X - w^i)
    //           * t(X) = sum_{ j } c_{i_j} * tau_j(X) for i_j in set_I
    //           * [zI]_2, [v]_1, [t]_1
    ///////////////////////////////////////////////////////////////////

    let start_step_4 = Instant::now();

    // Compute z_I(X)
    let now = Instant::now();
    let (zI_poly, zI_poly_tree) = get_vanishing_polynomial(&set_HI);
    println!("Time to get vanishing poly = {:?}", now.elapsed());

    // precompute values [a_1(xi_1)^{-1},... ,a_m(xi_m)] for a_i(X) = z_I(X) / (X - xi_i)
    let now = Instant::now();
    let lagrange_normalisers = get_lagrange_normalisers(&zI_poly, &zI_poly_tree);
    println!("Time to get lagrange normalisers = {:?}", now.elapsed());


    // Compute t(X)
    // t_evals[j] = c_{i_j}
    let mut t_evals = vec![];
    for j in 0..m {
        t_evals.push( witness.c_evals[ set_I[j] ] );
    }

    // interpolate t_evals over HI
    let t_poly = interpolate( &t_evals, &zI_poly_tree, &lagrange_normalisers );


    // COMMITMENTS

    // Commitment to zI(X) in Group 2
    assert!( pp.g2_powers.len() >= zI_poly.len(), "Not enough g2 powers for computing [zI(x)]_2" );
    let g2_zI = VariableBaseMSM::multi_scalar_mul(&pp.g2_powers, convert_to_bigints(&zI_poly.coeffs).as_slice()).into_affine();

    // Commitment to v(X) in Group 1
    assert!( pp.g1_powers.len() >= v_poly.len(), "Not enough g1 powers for computing [v(x)]_1" );
    let g1_v = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&v_poly.coeffs).as_slice()).into_affine();

    // Commitment to t(X) in Group 1
    assert!( pp.g1_powers.len() >= t_poly.len(), "Not enough g1 powers for computing [t(x)]_1" );
    let g1_t = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&t_poly.coeffs).as_slice()).into_affine();

    println!("Time for lookup step 4 = {:?}", start_step_4.elapsed());

    ///////////////////////////////////////////////////////////////////
    //5. Get hash challenges.
    ///////////////////////////////////////////////////////////////////
    let start_step_5 = Instant::now();
    /*transcript.append_element(b"g2_zI", &g2_zI);
    transcript.append_element(b"g1_v", &g1_v);
    transcript.append_element(b"g1_t", &g1_t);


   
   
    let alpha: Fr = transcript.get_and_append_challenge(b"alpha");*/

    println!("Time for lookup step 5 = {:?}", start_step_5.elapsed());

     ///5.1 SAFE
     safe_transcript.add_G2_element(&g2_zI);
     safe_transcript.add_G1_element(&g1_v);
     safe_transcript.add_G1_element(&g1_t);
     let alpha = safe_transcript.get_challenge(1)[0];

    ///////////////////////////////////////////////////////////////////
    //6. Compute D(X) = M(X, alpha) = sum_{j=1}^m mu_j(alpha)tau_{col(j)}(X)
    ///////////////////////////////////////////////////////////////////

    let start_step_6 = Instant::now();

    // first compute zI(0)
    let zIzero = zI_poly[0];

    // then find [ a_1 zI(0), ... , a_m zI(0) ]
    let mut tau_zero_inverse_vec = vec![];
    for j in 0..m {
        tau_zero_inverse_vec.push( lagrange_normalisers[j] * &zIzero );
    }
    // then find [ (a_1 zI(0) )^{-1}, ... , (a_m zI(0))^{-1} ]
    batch_inversion( &mut tau_zero_inverse_vec );

    // then set [ -xi_1 * (a_1 zI(0) )^{-1}, ... , -xi_m * (a_m zI(0))^{-1} ]
    for j in 0..m {
        tau_zero_inverse_vec[j] = - (set_HI[j] * &tau_zero_inverse_vec[j]);
    }

    ////
    // D(X) = sum_j mu_j(alpha) tau_{col(j)}(0)^{-1} tau_{col_j(X)}
    // Here phi(nu_j) =   t( h_{i_{col(j)}} ) where (X - h_{i_{col(j)}}) divides zI(X)
    ////

    // Compute in evaluation domain.  Initialise to 0 vector
    let mut d_evals = vec![];
    for _ in 0..m {
        d_evals.push(Fr::zero());
    }

    // d_evals[ col_j ] += mu_j(alpha) tau_{col(j)}(0)^{-1}
    for j in 0..m {
        let mut temp = pp.domain_m.size_as_field_element() * &pp.domain_m.element(m - j);
        temp = (alpha - &pp.domain_m.element(j)) * &temp;
        let mu_j_alpha = z_Vm.evaluate(&alpha) * &temp.inverse().unwrap();

        d_evals[ col[j] ] = mu_j_alpha * &tau_zero_inverse_vec[col[j]] + &d_evals[ col[j] ];
    }

    // interpolate over set_HI
    let d_poly = interpolate( &d_evals, &zI_poly_tree, &lagrange_normalisers );

    println!("Time for lookup step 6 = {:?}", start_step_6.elapsed());

    ///////////////////////////////////////////////////////////////////
    //7.  Find R(X), Q2(X) such that deg(R(X)) < m − 1, R(0) = 0, and
    //      D(X)t(X) − phi(alpha) = R(X) + zI(X)Q2(X)
    ///////////////////////////////////////////////////////////////////

    let start_step_7 = Instant::now();
    let phi_alpha = witness.phi_poly.evaluate(&alpha);

    // temp_poly(X) = D(X) t(X) - phi(alpha)
    let temp_poly = &(&d_poly * &t_poly) - &DensePolynomial::from_coefficients_slice(&[ phi_alpha ] );

    // D(X) t(X) - phi(alpha) = R(X) + Q2(X) zI(X)
    // Here q2(X) = q2_poly and r_poly = R(X)
    let ( q2_poly , r_poly ) = fast_divide_with_q_and_r( &temp_poly, &zI_poly).unwrap();


    // Check result is valid
    assert!(r_poly[0].is_zero(), "R(0) neq 0 in step 7");
    println!("Time for lookup step 7 = {:?}", start_step_7.elapsed());

    ///////////////////////////////////////////////////////////////////
    //8.   Output [D]_1 = [D(x)]_1, [R]_1 = [R(x)]_1, [Q2]_1 = [Q2(x)]_1,
    ///////////////////////////////////////////////////////////////////

    let start_step_8 = Instant::now();
    // Commitment to D(X) in Group 1
    assert!( pp.g1_powers.len() >= d_poly.len(), "Not enough g1 powers for computing [D(x)]_1" );
    let g1_D = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&d_poly.coeffs).as_slice()).into_affine();

    // Commitment to R(X) in Group 1
    assert!( pp.g1_powers.len() >= r_poly.len(), "Not enough g1 powers for computing [R(x)]_1" );
    let g1_R = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&r_poly.coeffs).as_slice()).into_affine();

    // Commitment to Q2(X) in Group 1
    assert!( pp.g1_powers.len() >= q2_poly.len(), "Not enough g1 powers for computing [Q2(x)]_1" );
    let g1_Q2 = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&q2_poly.coeffs).as_slice()).into_affine();

    println!("Time for lookup step 8 = {:?}", start_step_8.elapsed());

    ///////////////////////////////////////////////////////////////////
    //9. Get hash challenges.
    ///////////////////////////////////////////////////////////////////
    let start_step_9 = Instant::now();
    /*transcript.append_element(b"g1_D", &g1_D);
    transcript.append_element(b"g1_R", &g1_R);
    transcript.append_element(b"g1_Q2", &g1_Q2);

    let beta: Fr = transcript.get_and_append_challenge(b"beta");*/


    ///9.1 SAFE
    safe_transcript.add_G1_element(&g1_D);
    safe_transcript.add_G1_element(&g1_R);
    safe_transcript.add_G1_element(&g1_Q2);
    let beta = safe_transcript.get_challenge(1)[0];

    println!("Time for lookup step 9 = {:?}", start_step_9.elapsed());

    ///////////////////////////////////////////////////////////////////
    //10. Compute E(X) = M(beta, X) = sum_{j=1}^m mu_j(X)tau_{col(j)}(beta)
    //  and Q1(X) such that E(X)(beta v(X) − 1) + zI (beta)zI(0)−1 = zV(X)Q1(X)
    ///////////////////////////////////////////////////////////////////

    let start_step_10 = Instant::now();
    /////
    // Compute tau_j(beta) for all j
    // Use that tau_j(X) = a_j zI(X) / (X - xi_j) for a_j = lagrange_normalisers[j]
    // Then tau_j(beta) = a_j zI(beta) / (beta - xi_j)
    ////

    // first compute zI(beta)
    let zIbeta = zI_poly.evaluate( &beta );

    // then find [ beta - xi_1, ... , beta - xi_m ]
    let mut tau_beta_vec = vec![];
    for j in 0..m {
        tau_beta_vec.push( beta - set_HI[j] );
    }
    // then find [ ( beta - xi_1 )^{-1}, ... , ( beta - xi_m )^{-1} ]
    batch_inversion( &mut tau_beta_vec );

    // then set [ a_1 * zI(beta) * ( beta - xi_1 )^{-1}, ... , a_m * zI(beta) * (beta - xi_m)^{-1} ]
    for j in 0..m {
        tau_beta_vec[j] = zIbeta * &(lagrange_normalisers[j] * &tau_beta_vec[j]);
    }

    ////
    // E(X) = sum_j mu_j(X) tau_{col(j)}(0)^{-1} tau_{col_j(beta)}
    // Here phi(nu_j) =   t( h_{i_{col(j)}} ) where (X - h_{i_{col(j)}}) divides zI(X)
    ////
    let mut e_vals = vec![];
    for j in 0..m {
        e_vals.push( tau_zero_inverse_vec[col[j]] * &tau_beta_vec[ col[j] ] );
    }

    let e_poly = EvaluationsOnDomain::from_vec_and_domain(e_vals.clone(), pp.domain_m).interpolate();

    ////
    // Compute Q1(X)
    ////

    // zI(0)^{-1}
    let zIzero_inv = zIzero.inverse().unwrap();

    // set temp_poly = E(X) (beta v(X) - 1) + zI(beta)zI(0)^{-1}
    let mut temp_poly = &e_poly * &( &DensePolynomial::from_coefficients_slice(&[ beta.clone() ] ) * &v_poly);
    temp_poly = &temp_poly - &e_poly.clone();
    temp_poly = &temp_poly + &DensePolynomial::from_coefficients_slice(&[ zIbeta * &zIzero_inv ] );


    // Find q1_poly such that E(X) (beta v(X) - 1) + zI(beta)zI(0)^{-1} = Q1(X) zV(X)
    let (q1_poly, remainder) = fast_divide_with_q_and_r( &temp_poly, &z_Vm.clone() ).unwrap();

    // Check result is valid
    assert!(remainder.is_zero(), "zV(X) does not divide E(X)(beta v(X) - 1) + zI(beta)zI(0)^(-1) in Step 10");

    println!("Time for lookup step 10 = {:?}", start_step_10.elapsed());


    ///////////////////////////////////////////////////////////////////
    //11.   Output [E]_1 = [E(x)]_1, [Q1]_1 = [Q1(x)]_1,
    ///////////////////////////////////////////////////////////////////

    let start_step_11 = Instant::now();
    // Commitment to E(X) in Group 1
    assert!( pp.g1_powers.len() >= e_poly.len(), "Not enough g1 powers for computing [E(x)]_1" );
    let g1_E = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&e_poly.coeffs).as_slice()).into_affine();

    // Commitment to Q1(X) in Group 1
    assert!( pp.g1_powers.len() >= q1_poly.len(), "Not enough g1 powers for computing [Q1(x)]_1" );
    let g1_Q1 = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&q1_poly.coeffs).as_slice()).into_affine();

    println!("Time for lookup step 11 = {:?}", start_step_11.elapsed());

    ///////////////////////////////////////////////////////////////////
    //12. Get hash challenges.
    ///////////////////////////////////////////////////////////////////
    let start_step_12 = Instant::now();
    /*transcript.append_element(b"g1_E", &g1_E);
    transcript.append_element(b"g1_Q1", &g1_Q1);

    let rho: Fr = transcript.get_and_append_challenge(b"rho");
    let gamma: Fr = transcript.get_and_append_challenge(b"gamma");*/

     ///12.1 SAFE
     safe_transcript.add_G1_element(&g1_E);
     safe_transcript.add_G1_element(&g1_Q1);
     let rho = safe_transcript.get_challenge(1)[0];
     let gamma = safe_transcript.get_challenge(1)[0];
     let delta = safe_transcript.get_challenge(1)[0];
     safe_transcript.finalize();

    println!("Time for lookup step 12 = {:?}", start_step_12.elapsed());

    ///////////////////////////////////////////////////////////////////
    //13. Run Caulk+ to show that g2_zI and g1_t are correct
    //    Compute ([a1]1, [a2]1, _ ) = ProverC+(t(X), HI ) and set [a]1 = [a1]1 + gamma[a2]1
    ///////////////////////////////////////////////////////////////////
    let start_step_13 = Instant::now();
    let caulkp_instance = CaulkpInstance {m: m, g1_C: instance.g1_C, g1_t: g1_t, g2_zI: g2_zI};

    let caulkp_witness = CaulkpWitness {set_I: set_I.clone(), t_poly: t_poly.clone(), zI_poly: zI_poly.clone(), lagrange_normalisers: lagrange_normalisers.clone()};

    let (g1_a1, g1_a2, _ ) = caulkp_prove(pp, input, &caulkp_instance, &caulkp_witness);

    let g1_a = g1_a1 +  g1_a2.mul( gamma.clone() ).into_affine();

    println!("Time for lookup step 13 = {:?}", start_step_13.elapsed());

    ///////////////////////////////////////////////////////////////////
    //14. Set u1 = E(alpha), u2 = phi(alpha),
    //    w1(X) = ( (E(X) - u1) / (X - alpha ) ) + gamma ( (phi(X) - u2) / (X - alpha) )
    ///////////////////////////////////////////////////////////////////
    let start_step_14 = Instant::now();

    let u1 = e_poly.evaluate( &alpha );
    let u2 = witness.phi_poly.evaluate( &alpha );

    let divisor = DensePolynomial::from_coefficients_vec(vec![-alpha.clone(), Fr::one()]);
    let numerator = e_poly.clone() + (&witness.phi_poly * gamma)  + DensePolynomial::from_coefficients_vec(vec![-u1 - gamma * u2]);

    let w1_poly = &numerator / &divisor;

    println!("Time for lookup step 14 = {:?}", start_step_14.elapsed());

    ///////////////////////////////////////////////////////////////////
    //15. Set u3 = zI(0)
    //    w2(X) = ( (zI(X) - u3) / X ) + gamma ( R(X) / X )
    //              + gamma^2 X^{d-m+1}( z_I(X) - X^m) + gamma^3 X^{d-m+1} R(X)
    ///////////////////////////////////////////////////////////////////

    let start_step_15 = Instant::now();
    let u3 = zI_poly.evaluate( &Fr::zero() );

    //w2(X) = (zI(X) - u3) / X
    let mut w2_poly = DensePolynomial::from_coefficients_vec((zI_poly[1..]).to_vec());

    //w2(X) = w2(X) + gamma r(X)/X
    w2_poly = w2_poly + DensePolynomial::from_coefficients_vec( (&r_poly * gamma)[1..].to_vec());

    // w2(X) = w2(X) +  X^{d-m+1} ( gamma^2  z_I(X)  + gamma^3  R(X))
    let gamma_sq = gamma * &gamma;
    let gamma_cubed = gamma * &gamma_sq;
    let mut shifted = vec![Fr::zero(); d - m + 1];	
    let mut w2_shifted_poly = &zI_poly * gamma_sq + &r_poly * gamma_cubed;

   // problem when running
   // shifted.extend_from_slice( &(&zI_poly * gamma_sq + &r_poly * gamma_cubed)[..] ); 

   // w2_poly = w2_poly + DensePolynomial::from_coefficients_vec(shifted);
	//println!("Size w2C = {:?}", w2_poly.len());

    // w2(X) = w2(X) - gamma^2 X^m
    w2_shifted_poly = DensePolynomial::from_coefficients_vec( w2_shifted_poly[..(w2_shifted_poly.len()-1)].to_vec() );
    println!("Size w2D = {:?}", w2_poly.len());

    println!("Time for lookup step 15 = {:?}", start_step_15.elapsed());

    ///////////////////////////////////////////////////////////////////
    //16.  Set P1(X) = t(X) D(beta) − phi(alpha) − R(X) − zI (beta) Q2(X), u4 = zI(beta)
    //      w3(X) = ( (D(X) - u1) / (X- beta) ) + gamma ( (zI(X) - u4)/(X - beta))
    //                  + gamma^2 ( P1(X) / (X - beta) )
    ///////////////////////////////////////////////////////////////////

    let start_step_16 = Instant::now();
    let u4 = zI_poly.evaluate( &beta );

    // P1(X) = t(X) u1 - r(X) - Q2(X) u4
    let mut p1_poly = &t_poly * u1 + &r_poly * (-Fr::one()) + &q2_poly * (-u4);

    // P1(X) = P1(X) - phi(alpha)
    p1_poly = p1_poly + DensePolynomial::from_coefficients_vec( [ -u2 ].to_vec() );

    // w3(X)
    let divisor = DensePolynomial::from_coefficients_vec(vec![-beta.clone(), Fr::one()]);
    let numerator = d_poly + (&zI_poly * gamma) + (&p1_poly * gamma_sq) + DensePolynomial::from_coefficients_vec(vec![-u1 - gamma * u4]);

    let w3_poly = &numerator / &divisor;
    println!("Time for lookup step 16 = {:?}", start_step_16.elapsed());

    ///////////////////////////////////////////////////////////////////
    //17. Set u5 = E(rho), P2(X) = E(rho)(beta v(X) − 1) + zI(beta) zI(0)^{−1} − zV(rho)Q1(X)
    //    w4(X) = ( (E(X) − u5) / ( X - rho) ) + gamma( P2(X) / (X - rho) )
    ///////////////////////////////////////////////////////////////////

    let start_step_17 = Instant::now();
    let u5 = e_poly.evaluate( &rho );

    // P2(X) = v(X) * beta * u5  - Q1(X) z_{Vm}(rho)
    let mut p2_poly = &v_poly * (beta * u5) + &q1_poly * (- z_Vm.evaluate( &rho ) );

    // P2(X) = P2(X) - u5 + zI(beta) zI(0)^{-1}
    p2_poly = p2_poly + DensePolynomial::from_coefficients_vec(vec![ -u5 + u4 * zIzero_inv ]);

    // w4(X)
    let divisor = DensePolynomial::from_coefficients_vec(vec![-rho.clone(), Fr::one()]);
    let numerator = e_poly + (&p2_poly * gamma) + DensePolynomial::from_coefficients_vec(vec![-u5]);

    let w4_poly = &numerator / &divisor;
    println!("Time for lookup step 17 = {:?}", start_step_17.elapsed());

    ///////////////////////////////////////////////////////////////////
    //18.  Set s = d − m + 1 for d the maximum power of x in srs and output
    //      u1, u2, u3, u4, u5,
    //      [a]_1, [w1]_1 = [w1(x)x^s]_1, [w2]_1 = [w2(x)]_1, [w3]_1 = [w3(x)]_1, [w4]_1 = [w4(x)]_1
    ///////////////////////////////////////////////////////////////////

    let start_step_18 = Instant::now();

    let s = d - m + 1;

    // Commitment to w1(X)X^{s} in Group 1
    assert!( pp.g1_powers[s..].len() >= w1_poly.len(), "Not enough g1 powers for computing [w1(x)x^s]_1" );
    let g1_w1 = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[s..], convert_to_bigints(&w1_poly.coeffs).as_slice()).into_affine();
	println!("Size w1 = {:?}", w1_poly.len());

    // Commitment to w2(X) in Group 1
    assert!( pp.g1_powers[..].len() >= w2_poly.len(), "Not enough g1 powers for computing [w2(x)]_1" );
    assert!( pp.g1_powers[s..].len() >= w2_shifted_poly.len(), "Not enough g1 powers for computing [w2_shifted(x)]_1" );
    let mut g1_w2 = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&w2_poly.coeffs).as_slice()).into_affine();
    let g1_w2_shifted = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[s..], convert_to_bigints(&w2_shifted_poly.coeffs).as_slice()).into_affine();
    g1_w2 = g1_w2 + g1_w2_shifted;
    

	println!("Size w2 = {:?}", w2_poly.len());


    // Commitment to w3(X) in Group 1
    assert!( pp.g1_powers.len() >= w3_poly.len(), "Not enough g1 powers for computing [w3(x)]_1" );
    let g1_w3 = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&w3_poly.coeffs).as_slice()).into_affine();
	println!("Size w3 = {:?}", w3_poly.len());

    // Commitment to w4(X) in Group 1
    assert!( pp.g1_powers.len() >= w4_poly.len(), "Not enough g1 powers for computing [w4(x)]_1" );
    let g1_w4 = VariableBaseMSM::multi_scalar_mul(&pp.g1_powers[..], convert_to_bigints(&w4_poly.coeffs).as_slice()).into_affine();
	println!("Size w4 = {:?}", w4_poly.len());

    println!("Time for lookup step 18 = {:?}", start_step_18.elapsed());

    let pi_lookup = LookupProof {
        g1_v: g1_v, g2_zI: g2_zI, g1_t: g1_t,
        //
        g1_D: g1_D, g1_R: g1_R, g1_Q2: g1_Q2,
        //
        g1_E: g1_E, g1_Q1: g1_Q1,
        //
        u1: u1, u2: u2, u3: u3, u4: u4, u5: u5,
        g1_a: g1_a,
        g1_w1: g1_w1, g1_w2: g1_w2, g1_w3: g1_w3, g1_w4: g1_w4
    };

    return pi_lookup

}


//The Baloo lookup verifier as described in Figure 6.
#[allow(non_snake_case)]
pub fn verify_lookup_proof(
    pp: &PublicParameters,
    instance: &LookupInstance,
    proof: &LookupProof,
)->bool
{
    ///////////////////////////////////////////////////////////////////
    //1. Parse inputs
    ///////////////////////////////////////////////////////////////////
    let m = instance.m.clone();
    let z_Vm: UniPoly381 = pp.domain_m.vanishing_polynomial().into();
    let d = pp.g1_powers.len() - 1;
    let s = d - m + 1;
    let g1 = pp.g1_powers[0];

    /*let mut transcript = BalooTranscript::new();
    transcript.append_element(b"m", &m);
    transcript.append_element(b"g1_C", &instance.g1_C);
    transcript.append_element(b"g1_phi", &instance.g1_phi);*/

     ///////////////////////////////////////////////////////////////////
    //1.1 Safe transcript initialization
    ///////////////////////////////////////////////////////////////////
    use crate:: baloo_transcript::{SigmaPattern,SigmaOp,BalooSafeTranscript};
    use neptune::sponge::vanilla::{Sponge,SpongeTrait,Mode};
    use neptune::{Strength}; 
    use blstrs::Scalar as FrBlst; 
    use generic_array::typenum;
    let pattern = SigmaPattern(vec![
        SigmaOp::SendF(1),
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::SendG2(1),
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::ReceiveF(1),//alpha
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::ReceiveF(1),//beta
        SigmaOp::SendG1(1),
        SigmaOp::SendG1(1),
        SigmaOp::ReceiveF(1),//rho
        SigmaOp::ReceiveF(1),//gamma
        SigmaOp::ReceiveF(1),//delta
    ]);
    let p = Sponge::<FrBlst, typenum::U3>::api_constants(Strength::Standard);
    let mut safe_transcript = BalooSafeTranscript::<Fr,FrBlst>::new_with_constants(&pattern, &p);
    safe_transcript.add_field_element(&Fr::from(m as i128));
    safe_transcript.add_G1_element(&instance.g1_C);
    safe_transcript.add_G1_element(&instance.g1_phi);


    ///////////////////////////////////////////////////////////////////
    //Get hash challenges.
    ///////////////////////////////////////////////////////////////////
   /*  transcript.append_element(b"g2_zI", &proof.g2_zI);
    transcript.append_element(b"g1_v", &proof.g1_v);
    transcript.append_element(b"g1_t", &proof.g1_t);

    let alpha: Fr = transcript.get_and_append_challenge(b"alpha");

    transcript.append_element(b"g1_D", &proof.g1_D);
    transcript.append_element(b"g1_R", &proof.g1_R);
    transcript.append_element(b"g1_Q2", &proof.g1_Q2);

    let beta: Fr = transcript.get_and_append_challenge(b"beta");

    transcript.append_element(b"g1_E", &proof.g1_E);
    transcript.append_element(b"g1_Q1", &proof.g1_Q1);

    let rho: Fr = transcript.get_and_append_challenge(b"rho");
    let gamma: Fr = transcript.get_and_append_challenge(b"gamma");

    

    let delta: Fr = transcript.get_and_append_challenge(b"delta");*/


    safe_transcript.add_G2_element(&proof.g2_zI);
     safe_transcript.add_G1_element(&proof.g1_v);
     safe_transcript.add_G1_element(&proof.g1_t);
     let alpha = safe_transcript.get_challenge(1)[0];

     safe_transcript.add_G1_element(&proof.g1_D);
    safe_transcript.add_G1_element(&proof.g1_R);
    safe_transcript.add_G1_element(&proof.g1_Q2);
    let beta = safe_transcript.get_challenge(1)[0];

    safe_transcript.add_G1_element(&proof.g1_E);
     safe_transcript.add_G1_element(&proof.g1_Q1);
     let rho = safe_transcript.get_challenge(1)[0];
     let gamma = safe_transcript.get_challenge(1)[0];
     let delta = safe_transcript.get_challenge(1)[0];
     safe_transcript.finalize();

     let gamma_sq = gamma * &gamma;
     let gamma_cubed = gamma_sq * &gamma;

    ///////////////////////////////////////////////////////////////////
    //Compute [P1]1 = u1[t]_1 − u2[1]_1 − [R]_1 − u4 [Q2]_1
    ///////////////////////////////////////////////////////////////////

    let g1_p1 = proof.g1_t.mul( proof.u1.clone() )
                    - g1.mul( proof.u2.clone() )
                    - proof.g1_R.into_projective()
                    - proof.g1_Q2.mul( proof.u4.clone() );

    ///////////////////////////////////////////////////////////////////
    //Compute [P2]_1 = u5 ( beta [v]_1 − [1]_1) + [u_3^{-1}u4]_1 - zV(rho) [Q1]_1
    ///////////////////////////////////////////////////////////////////

    let g1_p2 = proof.g1_v.mul( beta * proof.u5.clone() )
                    + g1.mul( proof.u3.inverse().unwrap() * proof.u4.clone()  - proof.u5.clone() )
                    - proof.g1_Q1.mul( z_Vm.evaluate( &rho ) );

    ///////////////////////////////////////////////////////////////////
    //1) e( (C − t) + gamma [zH(x)]_1, [1]_2 ) − e([a]_1, [zI]_2) = 0
    //      i.e. Check that C+ elements [a1]1 and [a2]1 verify
    ///////////////////////////////////////////////////////////////////

    // (C − t) + gamma [zH(x)]_1
    let mut pair_with_1 = instance.g1_C.into_projective() - proof.g1_t.into_projective() + pp.g1_zH.mul(gamma);

    // - [a]_1
    let mut pair_with_zI = proof.g1_a.mul(-Fr::one());

    ///////////////////////////////////////////////////////////////////
    //2) e( alpha[w1]_1, [1]_2)
    //      − e([w1]_1, [x]_2) + e([E]_1 + gamma cm − [u1 + gamma u2]_1, [x^s]_2) = 0
    //  i.e. Check that E(alpha) = u1, phi(alpha) = u2, deg(E(X)) < m
    ///////////////////////////////////////////////////////////////////

    // delta old + alpha [w1]_1
    pair_with_1 = pair_with_1.into_affine().mul( delta.clone() ) + proof.g1_w1.mul( alpha.clone() );

    // delta old
    pair_with_zI = pair_with_zI.into_affine().mul( delta.clone() );

    // - [w1]_1
    let mut pair_with_x = proof.g1_w1.mul( -Fr::one() );

    // [E]_1 + gamma cm − [u1 + gamma u2]_1
    let mut pair_with_x_s = proof.g1_E.into_projective() + instance.g1_phi.mul( gamma.clone() )
                + g1.mul( - proof.u1 - gamma * proof.u2 );


    ///////////////////////////////////////////////////////////////////
    //3. e(−[u3]_1 + gamma [R]_1, [1]_2) − e( [w2]_1, [x]_2 ) + e([1 + gamma^2 x^{s+1}]_1, [zI]_2)
    //        +e(−gamma^2[x^m]_1 + gamma^3 [R]_1, [x^{s+1}]_2) = 0
    //   i.e. Check that zI(0) = u3, R(0) = 0, deg(zI(X)) = m and deg(R(X))< m
    ///////////////////////////////////////////////////////////////////

    // delta old −[u3]_1 + gamma [R]_1
    pair_with_1 = pair_with_1.into_affine().mul( delta.clone() )
                - g1.mul( proof.u3.clone() ) + proof.g1_R.mul( gamma.clone() );

    // delta old + [1 + gamma^2 x^{s+1}]_1
    pair_with_zI = pair_with_zI.into_affine().mul( delta.clone() )
                    + g1.into_projective() + pp.g1_powers[s+1].mul( gamma_sq.clone() );

    // delta old - [w2]_1
    pair_with_x = pair_with_x.into_affine().mul( delta.clone() ) + proof.g1_w2.mul(-Fr::one());

    // delta old
    pair_with_x_s = pair_with_x_s.into_affine().mul( delta.clone() );

    // −gamma^2[x^m]_1 + gamma^3 [R]_1
    let mut pair_with_x_splus1 = pp.g1_powers[m].mul( -gamma_sq.clone() )
                + proof.g1_R.mul( gamma_cubed.clone() );


    ///////////////////////////////////////////////////////////////////
    //4. e( beta[w3]_1 + [D]_1 + gamma^2[P1]_1 − [u1 + gamma u4]_1, [1]_2)
    //      − e([w3]_1, [x]_2) + e([gamma]_1, [zI]_2) = 0
    //   i.e. Check that D(beta) = E(alpha), zI(beta) = u4, t(X)D(X) − phi(alpha) = R(X) + zI(X)Q2
    ///////////////////////////////////////////////////////////////////

    // delta old + beta[w3]_1 + [D]_1 + gamma^2[P1]_1 − [u1 + gamma u4]_1
    pair_with_1 = pair_with_1.into_affine().mul( delta.clone() )
                    + proof.g1_w3.mul( beta.clone() )
                    + proof.g1_D.into_projective()
                    + g1_p1.into_affine().mul(gamma_sq.clone())
                    - g1.mul( proof.u1 + gamma * proof.u4 );

    // delta old + [gamma]_1
    pair_with_zI = pair_with_zI.into_affine().mul( delta.clone() ) + g1.mul( gamma.clone() );

    // delta old - [w3]_1
    pair_with_x = pair_with_x.into_affine().mul( delta.clone() ) + proof.g1_w3.mul(-Fr::one());

    // delta old
    pair_with_x_s = pair_with_x_s.into_affine().mul( delta.clone() );

    // delta old
    pair_with_x_splus1 = pair_with_x_splus1.into_affine().mul( delta.clone() );

    ///////////////////////////////////////////////////////////////////
    //5. e( rho[w4]_1 + [E]_1 + gamma[P2]_1 − [u5]_1, [1]_2) − e([w4]_1, [x]_2) = 0
    //  i.e. Check that E(rho) = u5 and E(X)(beta v(X) − 1) + zI(beta)zI(0)^{−1} = zV(X)Q1(X)
    ///////////////////////////////////////////////////////////////////

    // delta old + rho[w4]_1 + [E]_1 + gamma[P2]_1 − [u5]_1
    pair_with_1 = pair_with_1.into_affine().mul( delta.clone() )
                    + proof.g1_w4.mul( rho.clone() )
                    + proof.g1_E.into_projective()
                    + g1_p2.into_affine().mul(gamma.clone())
                    - g1.mul( proof.u5 );

    // delta old
    pair_with_zI = pair_with_zI.into_affine().mul( delta.clone() );

    // delta old - [w4]_1
    pair_with_x = pair_with_x.into_affine().mul( delta.clone() ) + proof.g1_w4.mul(-Fr::one());

    // delta old
    pair_with_x_s = pair_with_x_s.into_affine().mul( delta.clone() );

    // delta old
    pair_with_x_splus1 = pair_with_x_splus1.into_affine().mul( delta.clone() );

    ///////////////////////////////////////////////////////////////////
    //5. Evaluate pairings
    ///////////////////////////////////////////////////////////////////

    let test_miller = Bls12_381::miller_loop(
    [
        (pair_with_1.into_affine().into(), pp.g2_powers[0].into()),
        (pair_with_zI.into_affine().into(), proof.g2_zI.into()),
        (pair_with_x.into_affine().into(), pp.g2_powers[1].into()),
        (pair_with_x_s.into_affine().into(), pp.g2_powers[s].into()),
        (pair_with_x_splus1.into_affine().into(), pp.g2_powers[s+1].into())
    ]
    .iter(),
    );

    let test = Bls12_381::final_exponentiation( &test_miller ).unwrap();

    return test.is_one()
}



#[cfg(test)]
pub mod tests{

    use crate::baloo_setup::{setup_lookup,get_poly_and_g1_openings};
    use crate::{LookupProverInput, LookupInstance, LookupWitness,compute_lookup_proof,verify_lookup_proof};
    use std::time::Instant;
    use rand::Rng;
    use ark_poly::EvaluationDomain;
    use crate::EvaluationsOnDomain;
    use crate::tools::{convert_to_bigints};
    use ark_ec::{msm::VariableBaseMSM,ProjectiveCurve};

    #[allow(non_snake_case)]
    pub fn do_multiple_lookups()
    {
        const MIN_LOG_N: usize  = 7;
        const MAX_LOG_N: usize = 12;
        const EPS: usize=1;
        const MIN_LOG_M: usize=2;
        const MAX_LOG_M: usize=5;

        for n in MIN_LOG_N..=MAX_LOG_N
        {

            //1. Setup
            let N: usize = 1<<n;
            let powers_size: usize = 2*N; //SRS SIZE
            println!("N={}",N);
            let temp_m = n; //dummy
            let now = Instant::now();
            let mut pp =setup_lookup(&powers_size,&N,&temp_m,&n);
            let actual_degree = N-EPS;
            println!("time for powers of tau {:?} for N={:?}", now.elapsed(),N);

            //2. Poly and openings
            let table=get_poly_and_g1_openings(&pp,actual_degree);

            for logm in MIN_LOG_M..=std::cmp::min(MAX_LOG_M,n/2-1)
            {
                //3. Setup
                let now = Instant::now();
                let mut m = 1<<logm;
                m = m + 1;

                println!("m={}",m);
                pp = setup_lookup(&powers_size, &N, &m, &n);
                println!("Time to generate aux domain {:?}", now.elapsed());

                    //4. Positions
                let mut rng = rand::thread_rng();
                let mut positions: Vec<usize> = vec![];
                for _ in 0..m {
                    //generate positions randomly in the set
                    let i_j: usize = rng.gen_range(0,actual_degree);
                    positions.push(i_j);
                };

                //5. generating phi
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


                //6. Running proofs
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

                let now = Instant::now();
                let lookup_proof = compute_lookup_proof(&pp, &prover_input, &lookup_instance, &lookup_witness );
                println!("Time to generate proof for = {:?}", now.elapsed());
                let now = Instant::now();
                let res = verify_lookup_proof(&pp, &lookup_instance, &lookup_proof);
                println!("Time to verify proof for  = {:?}",   now.elapsed());
                assert!(res);
                println!("Lookup test succeeded");
            }
        }

    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_multiple_lookups()
    {
        do_multiple_lookups()
    }

}
