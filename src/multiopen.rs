/*
This file includes an algorithm for calculating n openings of a KZG vector commitment of size n in n log(n) time.
The algorithm is by Feist and khovratovich.
It is useful for preprocessing.
The full algorithm is described here https://github.com/khovratovich/Kate/blob/master/Kate_amortized.pdf
*/

use std::str::FromStr;
//use std::time::{Instant};
use std::vec::Vec;


use ark_ff::{PrimeField, Fp256, Field};
use ark_poly::{univariate::DensePolynomial,EvaluationDomain, GeneralEvaluationDomain, UVPolynomial};
use ark_ec::{AffineCurve,ProjectiveCurve};
use ark_bls12_381::{Fr,FrParameters, G1Affine, G1Projective};

use ark_std::{Zero};




pub fn compute_h_opt_g1(
    c_poly: &DensePolynomial<Fp256<FrParameters>>,   //c(X) degree up to d<2^p , i.e. c_poly has at most d+1 coeffs non-zero
    g1powers: &Vec<G1Affine>,  //SRS
    p: usize
)->Vec<G1Projective>
{
    let mut coeffs = c_poly.coeffs().to_vec();
    let dom_size = 1<<p;
    let fpzero = Fp256::from_str("0").unwrap();
    coeffs.resize(dom_size,fpzero);


    //1. x_ext = [[x^(d-1)], [x^{d-2},...,[x],[1], d+2 [0]'s]
    let mut x_ext = vec![];
    for i in 0..=dom_size-2{
        x_ext.push( g1powers[dom_size-2-i].into_projective());
    }
    let g1inf = g1powers[0].mul(fpzero);
    x_ext.resize(2*dom_size,g1inf); //filling 2d+2 neutral elements

    let y = dft_g1_opt(&x_ext, p+1);

    //2. c_ext = [c_d, d zeroes, c_d,c_{0},c_1,...,c_{d-2},c_{d-1}]
    let mut c_ext = vec![];
    c_ext.push(coeffs[coeffs.len()-1]);
    c_ext.resize(dom_size,fpzero);
    c_ext.push(coeffs[coeffs.len()-1]);
    for i in 0..coeffs.len()-1{
        c_ext.push(coeffs[i]);
    }
    assert_eq!(c_ext.len(),2*dom_size);
    let v = dft_opt(&c_ext, p+1);

    //3. u = y o v
    let u = y.into_iter()
        .zip(v.into_iter())
        .map(|(a,b)|{a.mul(b.into_repr())})
        .collect();

    //4. h_ext = idft_{2d+2}(u)
    let h_ext = idft_g1_opt(&u, p+1);

    return h_ext[0..dom_size].to_vec();
}

//compute dft of size @dom_size over vector of G1 elements
//q_i = h_0 + h_1w^i + h_2w^{2i}+\cdots + h_{dom_size-1}w^{(dom_size-1)i} for 0<= i< dom_size=2^p
pub fn dft_g1_opt(
    h: &Vec<G1Projective>,
    p: usize
)->Vec<G1Projective>
{
    let dom_size = 1<<p;
    assert_eq!(h.len(),dom_size);  //we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size/2;
    let mut m: usize=1;
    //Stockham FFT
    let mut xprev = h.to_vec();
    for _ in 1..=p{
        let mut xnext= vec![];
        xnext.resize(xprev.len(),h[0]);
        for j in 0..l{
            for k in 0..m{
                    let c0 = xprev[k+j*m].clone();
                    let c1 = &xprev[k+j*m+l*m];
                    xnext[k+2*j*m] = c0+c1;
                    let wj_2l=input_domain.element((j*dom_size/(2*l))%dom_size);
                    xnext[k+2*j*m+m]= (c0-c1).mul(wj_2l.into_repr());
            }
        }
        l = l/2;
        m = m*2;
        xprev = xnext;
    }
    return xprev;
}

//compute dft of size @dom_size over vector of Fr elements
//q_i = h_0 + h_1w^i + h_2w^{2i}+\cdots + h_{dom_size-1}w^{(dom_size-1)i} for 0<= i< dom_size=2^p
pub fn dft_opt(
    h: &Vec<Fr>,
    p: usize
)->Vec<Fr>
{
    let dom_size = 1<<p;
    assert_eq!(h.len(),dom_size);  //we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size/2;
    let mut m: usize=1;
    //Stockham FFT
    let mut xprev = h.to_vec();
    for _ in 1..=p{
        let mut xnext= vec![];
        xnext.resize(xprev.len(),h[0]);
        for j in 0..l{
            for k in 0..m{
                    let c0 = xprev[k+j*m].clone();
                    let c1 = &xprev[k+j*m+l*m];
                    xnext[k+2*j*m] = c0+c1;
                    let wj_2l=input_domain.element((j*dom_size/(2*l))%dom_size);
                    xnext[k+2*j*m+m]= (c0-c1)*(wj_2l);
            }
        }
        l = l/2;
        m = m*2;
        xprev = xnext;
    }
    return xprev;
}


//compute idft of size @dom_size over vector of G1 elements
//q_i = (h_0 + h_1w^-i + h_2w^{-2i}+\cdots + h_{dom_size-1}w^{-(dom_size-1)i})/dom_size for 0<= i< dom_size=2^p
pub fn idft_g1_opt(
    h: &Vec<G1Projective>,
    p: usize
)->Vec<G1Projective>
{
    let dom_size = 1<<p;
    assert_eq!(h.len(),dom_size);  //we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size/2;
    let mut m: usize=1;
    let mut dom_fr = Fr::from_str("1").unwrap();
    //Stockham FFT
    let mut xprev = h.to_vec();
    for _ in 1..=p{
        let mut xnext= vec![];
        xnext.resize(xprev.len(),h[0]);
        for j in 0..l{
            for k in 0..m{
                    let c0 = xprev[k+j*m].clone();
                    let c1 = &xprev[k+j*m+l*m];
                    xnext[k+2*j*m] = c0+c1;
                    let wj_2l=input_domain.element((dom_size-(j*dom_size/(2*l))%dom_size)%dom_size);
                    xnext[k+2*j*m+m]= (c0-c1).mul(wj_2l.into_repr()); //Difference #1 to forward dft
            }
        }
        l = l/2;
        m = m*2;
        dom_fr = dom_fr+dom_fr;
        xprev=xnext;
    }
    let res = xprev
        .iter()
        .map(|x|{x
            .mul(dom_fr
                .inverse()
                .unwrap().into_repr())})
        .collect();
    return res;
}

//compute all openings to c_poly using a smart formula
pub fn multiple_open_g1(
    g1powers: &Vec<G1Affine>, //SRS
    c_poly: &DensePolynomial<Fp256<FrParameters>>,   //c(X)
    p: usize
)->Vec<G1Affine>
{
    let degree=c_poly.coeffs.len();
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(degree).unwrap();
    let dom_size = input_domain.size();

    assert_eq!(1<<p,dom_size);

    let mut c_poly_extend = c_poly.clone();
    while c_poly_extend.len() < dom_size {
        c_poly_extend.coeffs.push( Fr::zero() );
    }

    //let now = Instant::now();
    let h2 = compute_h_opt_g1(&c_poly_extend, g1powers, p);
    //println!("H2 computed in {:?}", now.elapsed());

    //let now = Instant::now();
    let q2 = dft_g1_opt(&h2,p);
    //println!("Q2 computed in {:?}", now.elapsed());

    let mut res: Vec<G1Affine> = vec![];
    for i in 0..dom_size{
        res.push(q2[i].into_affine());
    }
    return res;
}


#[cfg(test)]
pub mod tests {


    
    use ark_poly_commit::kzg10::*;
    use ark_bls12_381::{Bls12_381,G1Affine,G1Projective};
    use ark_ff::{Fp256};
    use ark_ec::{AffineCurve,ProjectiveCurve};
    use ark_poly::EvaluationDomain;
    use ark_poly::univariate::DensePolynomial;
    
    //use crate::caulk_multi_setup::{setup_multi_lookup, PublicParameters};
    use crate::multiopen::*;

    #[allow(dead_code)]
    pub fn commit_direct(
        c_poly: &DensePolynomial<Fp256<FrParameters>>,   //c(X)
        poly_ck: &Powers<Bls12_381>,  //SRS
    )-> G1Affine
    {
        assert!(c_poly.coeffs.len()<=poly_ck.powers_of_g.len());
        let mut com = poly_ck.powers_of_g[0].mul(c_poly.coeffs[0]);
        for i in 1..c_poly.coeffs.len()
        {
            com = com + poly_ck.powers_of_g[i].mul(c_poly.coeffs[i]);
        }
        return com.into_affine();
    }

    //compute dft of size @dom_size over vector of G1 elements
    //q_i = h_0 + h_1w^i + h_2w^{2i}+\cdots + h_{dom_size-1}w^{(dom_size-1)i} for 0<= i< dom_size=2^p
    #[allow(dead_code)]
    pub fn dft_g1_opt(
        h: &Vec<G1Projective>,
        p: usize
    )->Vec<G1Projective>
    {
        let dom_size = 1<<p;
        assert_eq!(h.len(),dom_size);  //we do not support inputs of size not power of 2
        let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
        let mut l = dom_size/2;
        let mut m: usize=1;
        //Stockham FFT
        let mut xprev = h.to_vec();
        for _ in 1..=p{
            let mut xnext= vec![];
            xnext.resize(xprev.len(),h[0]);
            for j in 0..l{
                for k in 0..m{
                        let c0 = xprev[k+j*m].clone();
                        let c1 = &xprev[k+j*m+l*m];
                        xnext[k+2*j*m] = c0+c1;
                        let wj_2l=input_domain.element((j*dom_size/(2*l))%dom_size);
                        xnext[k+2*j*m+m]= (c0-c1).mul(wj_2l.into_repr());
                }
            }
            l = l/2;
            m = m*2;
            xprev = xnext;
        }
        return xprev;
    }

    //compute idft of size @dom_size over vector of G1 elements
    //q_i = (h_0 + h_1w^-i + h_2w^{-2i}+\cdots + h_{dom_size-1}w^{-(dom_size-1)i})/dom_size for 0<= i< dom_size=2^p
    #[allow(dead_code)]
    pub fn idft_g1_opt(
        h: &Vec<G1Projective>,
        p: usize
    )->Vec<G1Projective>
    {
        let dom_size = 1<<p;
        assert_eq!(h.len(),dom_size);  //we do not support inputs of size not power of 2
        let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
        let mut l = dom_size/2;
        let mut m: usize=1;
        let mut dom_fr = Fr::from_str("1").unwrap();
        //Stockham FFT
        let mut xprev = h.to_vec();
        for _ in 1..=p{
            let mut xnext= vec![];
            xnext.resize(xprev.len(),h[0]);
            for j in 0..l{
                for k in 0..m{
                        let c0 = xprev[k+j*m].clone();
                        let c1 = &xprev[k+j*m+l*m];
                        xnext[k+2*j*m] = c0+c1;
                        let wj_2l=input_domain.element((dom_size-(j*dom_size/(2*l))%dom_size)%dom_size);
                        xnext[k+2*j*m+m]= (c0-c1).mul(wj_2l.into_repr()); //Difference #1 to forward dft
                }
            }
            l = l/2;
            m = m*2;
            dom_fr = dom_fr+dom_fr;
            xprev = xnext;
        }
        let res = xprev
            .iter()
            .map(|x|{x
                .mul(dom_fr
                    .inverse()
                    .unwrap().into_repr())})
            .collect();
        return res;
    }
}
