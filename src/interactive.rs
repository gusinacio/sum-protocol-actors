use std::fmt::Debug;

use sum_check::RandomGenerator;

pub mod sum_check;

pub trait Prover {
    type Challenge;
    type Message;

    fn init(&mut self) -> Self::Message;

    fn handle(&mut self, msg: &Self::Challenge) -> (Self::Message, ProofStatus);
}

#[derive(Debug, Clone, Copy)]
pub enum ProofStatus {
    WaitingChallenge,
    Final,
}

#[derive(Debug)]
pub enum VerificationStatus<T, E> {
    Accept,
    Reject(E),
    Challenge(T),
}

pub trait Verifier<T> {
    type Challenge;
    type Message;
    type Error;

    fn handle_full(
        &mut self,
        msg: &Self::Message,
        generator: &mut T,
        _proof_status: ProofStatus,
    ) -> VerificationStatus<Self::Challenge, Self::Error> {
        self.handle(msg, generator)
    }
    fn handle(
        &mut self,
        msg: &Self::Message,
        generator: &mut T,
    ) -> VerificationStatus<Self::Challenge, Self::Error>;
}

pub struct NoProver;
pub struct NoVerifier;
pub struct NoRandomGenerator;

pub struct InteractiveProof<P, V, R> {
    prover: P,
    verifier: V,
    random_generator: R,
}

impl InteractiveProof<NoProver, NoVerifier, NoRandomGenerator> {
    pub fn new() -> Self {
        InteractiveProof {
            prover: NoProver,
            verifier: NoVerifier,
            random_generator: NoRandomGenerator,
        }
    }
}

impl<P, V, R> InteractiveProof<P, V, R> {
    pub fn with_prover<NewProver>(self, prover: NewProver) -> InteractiveProof<NewProver, V, R> {
        InteractiveProof {
            prover,
            verifier: self.verifier,
            random_generator: self.random_generator,
        }
    }
    pub fn with_verifier<NewVerifier>(
        self,
        verifier: NewVerifier,
    ) -> InteractiveProof<P, NewVerifier, R> {
        InteractiveProof {
            prover: self.prover,
            verifier,
            random_generator: self.random_generator,
        }
    }
    pub fn with_random_generator<NewRandomGenerator>(
        self,
        random_generator: NewRandomGenerator,
    ) -> InteractiveProof<P, V, NewRandomGenerator> {
        InteractiveProof {
            prover: self.prover,
            verifier: self.verifier,
            random_generator,
        }
    }
}

impl<P, V, R> InteractiveProof<P, V, R>
where
    P: Prover,
    R: RandomGenerator<Output = P::Challenge, Message = P::Message>,
{
    /// Execute proof and verify at the same time
    pub fn create_proof(mut self) -> Vec<P::Message> {
        let mut proof = vec![];
        let mut msg = self.prover.init();
        let mut status = ProofStatus::WaitingChallenge;
        loop {
            self.random_generator.update_script(&msg);
            proof.push(msg);
            let challenge = match status {
                ProofStatus::WaitingChallenge => self.random_generator.generate_number(),
                ProofStatus::Final => break,
            };
            (msg, status) = self.prover.handle(&challenge);
        }

        proof
    }
}

impl<P, V, R> InteractiveProof<P, V, R>
where
    P: Prover,
    V: Verifier<R, Message = P::Message, Challenge = P::Challenge>,
    R: RandomGenerator<Message = P::Message>,
{
    /// Execute proof and verify at the same time
    pub fn execute_proof(mut self) -> Vec<P::Message> {
        let mut proof = vec![];
        let mut msg = self.prover.init();
        let mut status = ProofStatus::WaitingChallenge;
        loop {
            self.random_generator.update_script(&msg);
            let response = self
                .verifier
                .handle_full(&msg, &mut self.random_generator, status);
            proof.push(msg);
            let challenge = match (status, response) {
                (ProofStatus::Final, VerificationStatus::Accept) => break,
                (ProofStatus::WaitingChallenge, VerificationStatus::Challenge(challenge)) => {
                    challenge
                }
                (_, VerificationStatus::Reject(_)) => {
                    panic!("Verifier rejected while prover was waiting for challenge")
                }
                (ProofStatus::Final, VerificationStatus::Challenge(_)) => {
                    panic!("Verifier returned a challenge while prover has finished")
                }
                (ProofStatus::WaitingChallenge, VerificationStatus::Accept) => {
                    panic!("Verifier accepted while prover was waiting for challenge")
                }
            };
            (msg, status) = self.prover.handle(&challenge);
        }

        proof
    }
}

impl<P, V, R> InteractiveProof<P, V, R>
where
    V: Verifier<R>,
    R: RandomGenerator<Message = V::Message>,
{
    /// Verify if a given proof is true
    pub fn verify(mut self, proof: Vec<V::Message>) -> bool {
        let mut iter = proof.iter().peekable();
        while let Some(msg) = iter.next() {
            self.random_generator.update_script(msg);
            match self.verifier.handle_full(
                &msg,
                &mut self.random_generator,
                if iter.peek().is_some() {
                    ProofStatus::WaitingChallenge
                } else {
                    ProofStatus::Final
                },
            ) {
                VerificationStatus::Accept => return true,
                VerificationStatus::Reject(_) => {
                    return false;
                }
                VerificationStatus::Challenge(_) => {}
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use ark_poly::{
        multivariate::{SparseTerm, Term},
        DenseMVPolynomial, Polynomial,
    };

    use crate::{scalar::Fq, sum_poly, FiatShamirGenerator, MultiPoly, Oracle};

    use super::{
        sum_check::{SumCheckProver, SumCheckVerifier},
        *,
    };

    #[test_log::test]
    fn interactive_test() {
        let polynomial = MultiPoly::from_coefficients_vec(
            4,
            vec![
                (Fq::from(-1), SparseTerm::new(vec![(0, 1), (1, 1), (2, 1)])),
                (Fq::from(-1), SparseTerm::new(vec![(0, 1), (1, 1), (3, 1)])),
                (
                    Fq::from(1),
                    SparseTerm::new(vec![(0, 1), (1, 1), (2, 1), (3, 1)]),
                ),
                (Fq::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (Fq::from(1), SparseTerm::new(vec![(1, 1), (3, 1)])),
                (Fq::from(-1), SparseTerm::new(vec![(1, 1), (2, 1), (3, 1)])),
            ],
        );
        let h = sum_poly(&polynomial);

        let polynomial_num_vars = polynomial.num_vars();
        let polynomial_degree = polynomial.degree();
        let oracle = Oracle::new(polynomial.clone());

        let protocol = InteractiveProof::new()
            .with_prover(SumCheckProver::new(polynomial.clone()))
            .with_verifier(SumCheckVerifier::new(
                polynomial_degree,
                polynomial_num_vars,
                oracle,
                h,
            ))
            .with_random_generator(FiatShamirGenerator::default());
        let proof = protocol.execute_proof();

        let oracle = Oracle::new(polynomial.clone());
        let protocol = InteractiveProof::new()
            .with_verifier(SumCheckVerifier::new(
                polynomial_degree,
                polynomial_num_vars,
                oracle,
                h,
            ))
            .with_random_generator(FiatShamirGenerator::default());
        let verify_result = protocol.verify(proof);
        assert!(verify_result);
    }
}
