use ark_ff::{Fp64, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "17"]
#[generator = "3"]
pub struct FqConfig;

pub type Fq = Fp64<MontBackend<FqConfig, 1>>;
