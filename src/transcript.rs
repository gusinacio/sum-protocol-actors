use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use sha3::{Digest, Sha3_256};

use crate::scalar::Fq;

#[derive(Default)]
pub struct Transcript {
    current_digest: sha3::Sha3_256,
}

impl Transcript {
    pub fn append_transcript<M: CanonicalSerialize>(&mut self, data: &M) {
        let mut buffer = Vec::new();
        data.serialize_uncompressed(&mut buffer).unwrap();
        self.current_digest.update(&buffer);
    }

    pub fn challenge(&mut self) -> Fq {
        let mut bytes = [0u8; 8];
        self.fill_bytes(&mut bytes);
        Fq::from_be_bytes_mod_order(&bytes)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut digest = self.current_digest.clone();
        let mut output = digest.finalize();
        let output_size = Sha3_256::output_size();
        let mut ptr = 0;
        let mut digest_ptr = 0;
        while ptr < dest.len() {
            dest[ptr] = output[digest_ptr];
            ptr += 1usize;
            digest_ptr += 1;
            if digest_ptr == output_size {
                self.current_digest.update(output);
                digest = self.current_digest.clone();
                output = digest.finalize();
                digest_ptr = 0;
            }
        }
        self.current_digest.update(output);
    }
}
