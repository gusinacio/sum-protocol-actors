use ark_ff::{One, UniformRand, Zero};
use ark_poly::Polynomial;
use tracing::Level;

use crate::{
    gen_uni_polynomial, partial_eval, scalar::Fq, Challenge, MultiPoly, Oracle, Proof,
    VerificationError,
};

use super::{ProofStatus, Prover, VerificationStatus, Verifier};

pub struct SumCheckProver {
    polynomial: MultiPoly,
    point: Vec<Fq>,
}

impl SumCheckProver {
    pub fn new(polynomial: MultiPoly) -> Self {
        Self {
            polynomial,
            point: vec![],
        }
    }
}

impl Prover for SumCheckProver {
    type Challenge = Challenge;
    type Message = Proof;

    fn init(&mut self) -> Self::Message {
        let polynomial = gen_uni_polynomial(&self.polynomial, &[None]);
        Proof(polynomial)
    }

    fn handle(
        &mut self,
        Challenge { point }: &Self::Challenge,
    ) -> (Self::Message, super::ProofStatus) {
        // TODO there's a better way to generate this
        self.point.push(*point);
        let mut inputs: Vec<Option<Fq>> = self.point.iter().map(|&x| Some(x)).collect();
        inputs.push(None);

        if self.polynomial.num_vars == inputs.len() {
            (
                Proof(partial_eval(&self.polynomial, &inputs)),
                ProofStatus::Final,
            )
        } else {
            (
                Proof(gen_uni_polynomial(&self.polynomial, &inputs)),
                ProofStatus::WaitingChallenge,
            )
        }
    }
}

pub struct SumCheckVerifier {
    polynomial_degree: usize,
    polynomial_num_vars: usize,
    last_val: Fq,
    point: Vec<Fq>,

    oracle: Oracle,
}

pub trait RandomGenerator {
    type Output;
    type Message;
    fn generate_number(&mut self) -> Self::Output;
    fn update_script(&mut self, msg: &Self::Message);
}

impl SumCheckVerifier {
    pub fn new(
        polynomial_degree: usize,
        polynomial_num_vars: usize,
        oracle: Oracle,
        h: Fq,
    ) -> Self {
        Self {
            last_val: h,
            oracle,
            polynomial_num_vars,
            polynomial_degree,
            point: vec![],
        }
    }
}

impl<T> Verifier<T> for SumCheckVerifier
where
    T: RandomGenerator<Output = Challenge>,
{
    type Challenge = Challenge;
    type Message = Proof;
    type Error = VerificationError;

    fn handle(
        &mut self,
        Proof(polynomial_g): &Self::Message,
        random_generator: &mut T,
    ) -> VerificationStatus<Self::Challenge, VerificationError> {
        tracing::span!(Level::TRACE, "Verifier");
        // We don't need to check for variables because the typesystem assures there's only 1 variable

        // TODO maybe I need to check the degree of the variable instead of degree of the polynomial
        if polynomial_g.degree() > self.polynomial_degree {
            return VerificationStatus::Reject(VerificationError::DegreeTooBig);
        }
        let g_0 = polynomial_g.evaluate(&Fq::zero());
        let g_1 = polynomial_g.evaluate(&Fq::one());

        tracing::info!("Sum g0 + g1 = {}", g_0 + g_1);

        if g_0 + g_1 != self.last_val {
            return VerificationStatus::Reject(VerificationError::SumNotEqual {
                g_0,
                g_1,
                h: self.last_val,
            });
        }

        // generate a random point
        let Challenge {
            point: random_point,
        } = random_generator.generate_number();

        tracing::info!(%random_point, "Generate random point");
        self.last_val = polynomial_g.evaluate(&random_point);
        self.point.push(random_point);
        tracing::info!(
            eval = %self.last_val, "Polynomial evaluated at random point",
        );
        tracing::info!(
            eval = %self.last_val,
            point = ?self.point,
            "Polynomial evaluated at random point",
        );
        if self.point.len() == self.polynomial_num_vars {
            let eval = self.oracle.evaluate(&self.point);
            if eval == polynomial_g.evaluate(&random_point) {
                VerificationStatus::Accept
            } else {
                VerificationStatus::Reject(VerificationError::NotEqualOracle)
            }
        } else {
            VerificationStatus::Challenge(Challenge {
                point: random_point,
            })
        }
    }
}

impl RandomGenerator for crate::RandomGenerator {
    type Output = Fq;
    type Message = Proof;
    fn generate_number(&mut self) -> Fq {
        // return a challenge
        Fq::rand(&mut self.rng)
    }

    fn update_script(&mut self, _msg: &Self::Message) {
        // noop
    }
}

impl RandomGenerator for crate::FiatShamirGenerator {
    type Output = Challenge;
    type Message = Proof;
    fn generate_number(&mut self) -> Challenge {
        Challenge {
            point: self.transcript.challenge(),
        }
    }

    fn update_script(&mut self, msg: &Self::Message) {
        self.transcript.append_transcript(msg);
    }
}
