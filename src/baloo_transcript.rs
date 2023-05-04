use ark_ff::BigInteger;
use ark_ff::BigInteger128;
use ark_ff::Fp256;
use ark_ff::PrimeField as ArkField;

use ark_serialize::CanonicalSerialize;
use merlin::Transcript;
use std::marker::PhantomData;
use std::mem::transmute; 
use blstrs::Scalar as FrBlst; 
use ff::PrimeField as FfField;
use generic_array::typenum;
use ark_bls12_381::{G1Affine,G2Affine};

pub struct BalooTranscript<F: ArkField> {
    transcript: Transcript,
    phantom: PhantomData<F>,
}

impl<F: ArkField> Default for BalooTranscript<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: ArkField> BalooTranscript<F> {
    pub fn new() -> Self {
        Self {
            transcript: Transcript::new(b"Init Baloo transcript"),
            phantom: PhantomData::default(),
        }
    }

    /// Get a uniform random field element for field size < 384
    pub fn get_and_append_challenge(&mut self, label: &'static [u8]) -> F {
        let mut bytes = [0u8; 64];
        self.transcript.challenge_bytes(label, &mut bytes);
        let challenge = F::from_le_bytes_mod_order(bytes.as_ref());
        self.append_element(b"append challenge", &challenge);
        challenge
    }

    /// Append a field/group element to the transcript
    pub fn append_element<T: CanonicalSerialize>(&mut self, label: &'static [u8], r: &T) {
        let mut buf = vec![];
        r.serialize(&mut buf).unwrap();
        self.transcript.append_message(label, buf.as_ref());
    }


}

use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::vanilla::{Sponge,SpongeTrait,Mode};
use neptune::{Strength}; 
use neptune::poseidon::{PoseidonConstants,Arity}; 

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SigmaOp {
    SendF(u32),
    SendG1(u32),
    SendG2(u32),
    ReceiveF(u32),
}

#[derive(Clone, Debug)]
pub struct SigmaPattern(pub Vec<SigmaOp>);

pub struct BalooSafeTranscript<'a, F: ArkField, F2:  FfField> {
    transcript: Transcript,
    phantom: PhantomData<F>,
    sponge: Sponge<'a, F2, typenum::U3> 
}



impl<'a, F: ArkField, F2:  FfField> BalooSafeTranscript<'a, F,F2>{
    const G1_in_F2:u32 = 6;
    const G2_in_F2:u32 = 12;

    //Creates new transcript from IOPattern and Poseidon constants //should be created on the fly
    pub fn new_with_constants(pattern: &SigmaPattern, constants: &'a PoseidonConstants<F2,typenum::U3>) -> Self {
        let mut sponge = Sponge::new_with_constants(constants, Mode::Simplex);
        let acc = &mut ();

        let io_pattern: Vec<SpongeOp> = pattern.0
            .iter()
            .map( |x|
            {
                match x{
                    SigmaOp::SendF(v) =>  {SpongeOp::Absorb(*v)},
                    SigmaOp::SendG1(v) =>  SpongeOp::Absorb(*v * Self::G1_in_F2),
                    SigmaOp::SendG2(v) =>  SpongeOp::Absorb(*v* Self::G2_in_F2),
                    SigmaOp::ReceiveF(v) =>  SpongeOp::Squeeze(*v)
                }
            }
            )
            .collect();

        sponge.start(IOPattern(io_pattern), 
            None, acc);
        Self {
            transcript: Transcript::new(b"Init Baloo transcript"),
            phantom: PhantomData::default(),
            sponge: sponge 
        }
    }

    pub fn convert_F_to_F2(elt: &F)-> F2{
        let mut val = elt   //Converting F to a vector of u64 and then to vector of vector of bytes
            .into_repr()
            .as_ref()
            .to_vec();
        let mut val2: Vec<Vec<u8>> = val
            .iter()
            .map(
                |x|
                {
                   x.to_le_bytes().to_vec()
                }
            )
            .collect();
        let mut un: Vec<u8> = Vec::new();
        for v  in val2{
            un.extend(v.iter());
        } 
        let mut def: F2::Repr = F2::default().to_repr();
        assert_eq!(def.as_ref().len(),un.len());
        def.as_mut().copy_from_slice(&un);
        F2::from_repr(def).unwrap()    
    }

    

    pub fn convert_F2_to_F(elt: &F2)->F{
        F::from_le_bytes_mod_order(&elt.to_repr().as_ref().to_vec())
    }

    //adding F element to the transcript
    pub fn add_field_element(&mut self, elt: &F){
        SpongeAPI::absorb( &mut self.sponge,
                 1,
                &[Self::convert_F_to_F2(elt)],
                &mut ());
    }

    //adding a few field elements to the transcript
    pub fn add_elements(&mut self, elts: &[F]){
        let vals: Vec<F2> = elts.
            iter().
            map(           |x| Self::convert_F_to_F2(x)                  )
            .collect();
        SpongeAPI::absorb( &mut self.sponge,
                 elts.len() as u32,
                &vals,
                &mut ());
    }

    //Get verifier challenge
    pub fn get_challenge(&mut self, length: u32)->Vec<F>{
        let out = SpongeAPI::squeeze(&mut self.sponge, length,&mut ())
            .iter()
            .map(|v| {Self::convert_F2_to_F(v)})
            .collect();
        //let mut v = out[0].to_repr();
        //let q = v.as_ref().to_vec();
        //F::from_be_bytes_mod_order(&q)
        out
    }

    pub fn convert_G1_to_vec(elt: &G1Affine)->Vec<F2>
    {
        let mut val: Vec<u64> = elt.x   //Converting F to a vector of u64 and then to vector of vector of bytes
        .into_repr()
        .as_ref()
        .to_vec();
        let mut valy = elt.y
            .into_repr()
            .as_ref()
            .to_vec();
        val.append(&mut valy);
        let mut val2: Vec<Vec<u8>> = val
            .iter()
            .map(
                |x|
                {
                x.to_le_bytes().to_vec()
                }
            )
            .collect();
        let mut un: Vec<u8> = Vec::new();
        for v  in val2{
            un.extend(v.iter());
        }

        //padding the vector to integer number of felts
        let mut def: F2::Repr = F2::default().to_repr();
        let f2_len = def.as_ref().len()/2;  //split G1 coordinates into 128 bit chunks
        let ceil_felts = (un.len()+f2_len-1)/f2_len;
        un.resize(ceil_felts*f2_len, 0u8);
        
        //creating F2s
        let mut vals = vec![];
        for i in 0..ceil_felts{
            let (left,_) =  def.as_mut().split_at_mut(f2_len);
            left.copy_from_slice(&un[i*f2_len..(i+1)*f2_len]);
            vals.push(F2::from_repr(def).unwrap());
        }
        assert_eq!(ceil_felts as u32,Self::G1_in_F2);
        vals
    }

    //add G1 element to the transcript . Each coordinate is viewed in bits and splitted into two chunks.
    pub fn add_G1_element(&mut self, elt: &G1Affine)
    {
        let vals = Self::convert_G1_to_vec(elt);
        SpongeAPI::absorb( &mut self.sponge,
            vals.len() as u32,
           &vals,
           &mut ()); 
    }

    pub fn convert_G2_to_vec(elt: &G2Affine)->Vec<F2>
    {
        let mut buf  = vec![];
        elt.x    
        .serialize(&mut buf).unwrap();
        let mut buf2  = vec![];
        elt.y    
        .serialize(&mut buf2).unwrap();
        
        buf.extend( buf2.iter()); 
        //padding the vector to integer number of felts
        let mut def: F2::Repr = F2::default().to_repr();
        let f2_len = def.as_ref().len()/2;  //split G2 coordinates into 128 bit chunks
        let ceil_felts = (buf.len()+f2_len-1)/f2_len;
        buf.resize(ceil_felts*f2_len, 0u8);
        
        //creating F2s
        let mut vals = vec![];
        for i in 0..ceil_felts{
            let (left,_) =  def.as_mut().split_at_mut(f2_len);
            left.copy_from_slice(&buf[i*f2_len..(i+1)*f2_len]);
            vals.push(F2::from_repr(def).unwrap());
        }
        assert_eq!(ceil_felts as u32,Self::G2_in_F2);
        vals
    }

    //add G2 element to the transcript. Each coordinate is converted to string and splitted into 64-symbol chunks
    pub fn add_G2_element(&mut self, elt: &G2Affine)
    {

        let vals = Self::convert_G2_to_vec(elt);
        SpongeAPI::absorb( &mut self.sponge,
            vals.len() as u32,
           &vals,
           &mut ()); 
    }

    pub fn finalize(&mut self)
    {
        self.sponge.finish(&mut ()).unwrap();
    }
}


#[cfg(test)]
pub mod tests{
    
    use blstrs::Scalar as FrBlst;  
    use ark_bls12_381::Fr as Fr;
 

    #[test]
    fn test_conversion()
    {
        use crate:: baloo_transcript::{SigmaPattern,SigmaOp,BalooSafeTranscript};
        let x = FrBlst::from(123);
        let x_f: Fr = BalooSafeTranscript::convert_F2_to_F(&x);
        let x_f2 = BalooSafeTranscript::convert_F_to_F2(&x_f);
        assert_eq!(x,x_f2);
    }

    
}