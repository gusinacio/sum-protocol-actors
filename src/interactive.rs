pub trait Prover {
    type Challenge;
    type Message;

    fn init(&mut self) -> Self::Message;

    fn handle(&mut self, msg: &Self::Challenge) -> (Self::Message, ProofStatus);
}

#[derive(Debug)]
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

pub trait Verifier {
    type Challenge;
    type Message;

    fn handle_full(
        &mut self,
        msg: &Self::Message,
        _proof_status: ProofStatus,
    ) -> VerificationStatus<Self::Challenge, ()> {
        self.handle(msg)
    }

    fn handle(&mut self, msg: &Self::Message) -> VerificationStatus<Self::Challenge, ()>;
}

pub struct NoProver;
pub struct NoVerifier;

pub struct InteractiveProof<P, V> {
    prover: P,
    verifier: V,
}

impl InteractiveProof<NoProver, NoVerifier> {
    pub fn new() -> Self {
        InteractiveProof {
            prover: NoProver,
            verifier: NoVerifier,
        }
    }
}

impl<P, V> InteractiveProof<P, V> {
    pub fn with_prover<NewProver>(self, prover: NewProver) -> InteractiveProof<NewProver, V> {
        InteractiveProof {
            prover,
            verifier: self.verifier,
        }
    }
    pub fn with_verifier<NewVerifier>(
        self,
        verifier: NewVerifier,
    ) -> InteractiveProof<P, NewVerifier> {
        InteractiveProof {
            prover: self.prover,
            verifier,
        }
    }
}

impl<P, V> InteractiveProof<P, V>
where
    P: Prover,
    V: Verifier<Message = P::Message, Challenge = P::Challenge>,
{
    /// Execute proof and verify at the same time
    pub fn create_proof(mut self) -> Vec<P::Message> {
        let mut proof = vec![];
        let mut msg = self.prover.init();
        let mut status = ProofStatus::WaitingChallenge;
        loop {
            let challenge = match status {
                ProofStatus::Final => match self.verifier.handle_full(&msg, status) {
                    VerificationStatus::Accept => {
                        proof.push(msg);
                        break;
                    }
                    VerificationStatus::Reject(_) => {
                        panic!("Verifier rejected while prover was waiting for challenge")
                    }
                    VerificationStatus::Challenge(_) => {
                        panic!("Verifier rejected while prover was waiting for challenge")
                    }
                },
                ProofStatus::WaitingChallenge => match self.verifier.handle_full(&msg, status) {
                    VerificationStatus::Accept => {
                        panic!("Verifier accepted while prover was waiting for challenge")
                    }
                    VerificationStatus::Reject(_) => {
                        panic!("Verifier rejected while prover was waiting for challenge")
                    }
                    VerificationStatus::Challenge(challenge) => {
                        proof.push(msg);
                        challenge
                    }
                },
            };
            let (new_msg, new_status) = self.prover.handle(&challenge);
            msg = new_msg;
            status = new_status;
        }

        proof
    }
}

impl<P, V> InteractiveProof<P, V>
where
    V: Verifier,
{
    /// Verify if a given proof is true
    pub fn verify(mut self, proof: Vec<V::Message>) -> bool {
        let mut iter = proof.iter().peekable();
        while let Some(msg) = iter.next() {
            match self.verifier.handle_full(
                &msg,
                if iter.peek().is_some() {
                    ProofStatus::WaitingChallenge
                } else {
                    ProofStatus::Final
                },
            ) {
                VerificationStatus::Accept => return true,
                VerificationStatus::Reject(_) => return false,
                VerificationStatus::Challenge(_) => {}
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct SumCheckProver;

    impl Prover for SumCheckProver {
        type Challenge = i32;

        type Message = i32;

        fn init(&mut self) -> Self::Message {
            todo!()
        }

        fn handle(&mut self, msg: &Self::Challenge) -> (Self::Message, ProofStatus) {
            todo!()
        }
    }
    struct SumCheckVerifier;
    impl Verifier for SumCheckVerifier {
        type Challenge = i32;

        type Message = i32;

        fn handle(&mut self, msg: &Self::Message) -> VerificationStatus<Self::Challenge, ()> {
            todo!()
        }
    }

    #[test]
    fn interactive_test() {
        let protocol = InteractiveProof::new()
            .with_prover(SumCheckProver)
            .with_verifier(SumCheckVerifier);
        let proof = protocol.create_proof();

        let protocol = InteractiveProof::new().with_verifier(SumCheckVerifier);
        let verify_result = protocol.verify(proof);
    }
}
