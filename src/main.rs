use ark_ff::{Field, One, UniformRand, Zero};
use ark_poly::{
    multivariate::{SparsePolynomial as SparseMultilinearPolynomial, SparseTerm, Term},
    univariate::DensePolynomial as UniPoly,
    DenseMVPolynomial, DenseUVPolynomial, Polynomial,
};
use ark_serialize::CanonicalSerialize;
use itertools::Itertools;
use kameo::{
    actor::ActorRef,
    message::{Context, Message as ActorMessage},
    Actor, Reply,
};

mod interactive;
mod polynomial;
mod scalar;
mod transcript;

use scalar::Fq;
use transcript::Transcript;

type MultiPoly = SparseMultilinearPolynomial<Fq, SparseTerm>;

#[derive(Actor)]
struct Oracle {
    polynomial: MultiPoly,
}

impl Oracle {
    pub fn new(polynomial: MultiPoly) -> Self {
        Self { polynomial }
    }
}

struct Evaluate(Vec<Fq>);

#[derive(Reply)]
struct Evaluation(Fq);

impl ActorMessage<Evaluate> for Oracle {
    type Reply = Evaluation;
    async fn handle(
        &mut self,
        Evaluate(point): Evaluate,
        _ctx: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        Evaluation(self.polynomial.evaluate(&point))
    }
}

#[derive(Actor)]
struct Verifier<T: Actor> {
    polynomial_degree: usize,
    polynomial_num_vars: usize,
    last_val: Fq,
    point: Vec<Fq>,

    oracle: ActorRef<Oracle>,
    random_generator: ActorRef<T>,
}

impl<T> Verifier<T>
where
    // any actor that returns a random number
    T: Actor + ActorMessage<GenerateNumber, Reply = RandomNumber>,
{
    pub fn new(polynomial: MultiPoly, h: Fq, random_generator: ActorRef<T>) -> Self {
        let polynomial_num_vars = polynomial.num_vars();
        let polynomial_degree = polynomial.degree();
        let oracle = kameo::spawn(Oracle::new(polynomial));
        Self {
            random_generator,
            last_val: h,
            oracle,
            polynomial_num_vars,
            polynomial_degree,
            point: vec![],
        }
    }

    async fn generate_random_number(&self) -> Fq {
        let RandomNumber(random_point) = self.random_generator.ask(GenerateNumber).await.unwrap();
        random_point
    }
}

#[derive(Clone, Debug, Reply, CanonicalSerialize)]
struct Proof(UniPoly<Fq>);

#[derive(thiserror::Error, Debug)]
enum VerificationError {
    #[error("Degree is too big")]
    DegreeTooBig,
    #[error("Sum is not equal. g_0: {g_0}, g_1: {g_1}, h: {h}")]
    SumNotEqual { g_0: Fq, g_1: Fq, h: Fq },
    #[error("Result is not equal from oracle")]
    NotEqualOracle,
}

#[derive(Debug, Reply)]
enum VerificationStatus {
    Accept,
    Reject(VerificationError),
    Challenge(Fq),
}

impl<T> ActorMessage<Proof> for Verifier<T>
where
    T: Actor + ActorMessage<GenerateNumber, Reply = RandomNumber>,
{
    type Reply = VerificationStatus;

    async fn handle(
        &mut self,
        Proof(polynomial_g): Proof,
        _ctx: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        // We don't need to check for variables because the typesystem assures there's only 1 variable

        // TODO maybe I need to check the degree of the variable instead of degree of the polynomial
        if polynomial_g.degree() > self.polynomial_degree {
            return VerificationStatus::Reject(VerificationError::DegreeTooBig);
        }
        let g_0 = polynomial_g.evaluate(&Fq::zero());
        let g_1 = polynomial_g.evaluate(&Fq::one());

        println!("[Verifier] Sum g0 + g1 = {}", g_0 + g_1);

        if g_0 + g_1 != self.last_val {
            return VerificationStatus::Reject(VerificationError::SumNotEqual {
                g_0,
                g_1,
                h: self.last_val,
            });
        }

        // generate a random point
        let random_point = self.generate_random_number().await;

        println!("[Verifier] Random point = {}", random_point);
        self.last_val = polynomial_g.evaluate(&random_point);
        self.point.push(random_point);
        println!(
            "[Verifier] Polynomial evaluated at random point = {}",
            self.last_val
        );
        println!("[Verifier] Point[] = {:?}", self.point);
        if self.point.len() == self.polynomial_num_vars {
            let Evaluation(eval) = self.oracle.ask(Evaluate(self.point.clone())).await.unwrap();
            if eval == polynomial_g.evaluate(&random_point) {
                VerificationStatus::Accept
            } else {
                VerificationStatus::Reject(VerificationError::NotEqualOracle)
            }
        } else {
            VerificationStatus::Challenge(random_point)
        }
    }
}

#[derive(Actor)]
struct RandomGenerator;

#[derive(Actor, Default)]
struct FiatShamirGenerator {
    transcript: Transcript,
}

struct GenerateNumber;

struct UpdateTranscript<M> {
    msg: M,
}

#[derive(Reply)]
struct RandomNumber(Fq);

impl<M: CanonicalSerialize + Send + 'static> ActorMessage<UpdateTranscript<M>>
    for FiatShamirGenerator
{
    type Reply = ();

    async fn handle(
        &mut self,
        UpdateTranscript { msg }: UpdateTranscript<M>,
        _: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        self.transcript.append_transcript(&msg);
    }
}

impl ActorMessage<GenerateNumber> for FiatShamirGenerator {
    type Reply = RandomNumber;

    async fn handle(
        &mut self,
        _: GenerateNumber,
        _: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        RandomNumber(self.transcript.challenge())
    }
}

impl ActorMessage<GenerateNumber> for RandomGenerator {
    type Reply = RandomNumber;

    async fn handle(
        &mut self,
        _: GenerateNumber,
        _: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        let mut rng = ark_std::rand::thread_rng();
        // return a challenge
        RandomNumber(Fq::rand(&mut rng))
    }
}

#[derive(Actor)]
struct Prover {
    polynomial: MultiPoly,
    point: Vec<Fq>,
}

impl Prover {
    pub fn new(polynomial: MultiPoly) -> Self {
        Self {
            polynomial,
            point: vec![],
        }
    }
}

/// initial step
struct RequestProof;
impl ActorMessage<RequestProof> for Prover {
    type Reply = ProofStatus;

    async fn handle(
        &mut self,
        _msg: RequestProof,
        _ctx: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        let polynomial = gen_uni_polynomial(&self.polynomial, &[None]);
        ProofStatus::WaitingForChallenge(Proof(polynomial))
    }
}

fn partial_eval(poly: &MultiPoly, vals: &[Option<Fq>]) -> UniPoly<Fq> {
    poly.terms
        .iter()
        // for each term
        .map(|(coef, term)| {
            let (coef, degree) =
                term.iter()
                    .fold((*coef, 0), |acc, (var, degree)| match vals[*var] {
                        Some(val) => (val.pow([(*degree) as u64]) * acc.0, acc.1),
                        None => (acc.0, *degree),
                    });
            // create a vector with size degree + 1 filled with zero
            let mut vec = vec![Fq::zero(); degree + 1];
            // set the coefficient to degree
            vec[degree] = coef;
            UniPoly::from_coefficients_vec(vec)
        })
        .fold(UniPoly::zero(), |acc, poly| acc + poly)
}
fn gen_uni_polynomial(poly: &MultiPoly, inputs: &[Option<Fq>]) -> UniPoly<Fq> {
    (0..poly.num_vars - inputs.len())
        .map(|_| [Fq::zero(), Fq::one()])
        .multi_cartesian_product()
        .map(|x| {
            let mut v = inputs.to_vec();
            v.extend(x.into_iter().map(Some));
            v
        })
        .fold(UniPoly::zero(), |acc, vals| acc + partial_eval(poly, &vals))
}

struct Challenge {
    point: Fq,
}

#[derive(Clone, Debug, Reply)]
enum ProofStatus {
    WaitingForChallenge(Proof),
    FinalProof(Proof),
}

impl ProofStatus {
    fn proof(self) -> Proof {
        match self {
            ProofStatus::WaitingForChallenge(proof) | ProofStatus::FinalProof(proof) => proof,
        }
    }
}

impl CanonicalSerialize for ProofStatus {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        match self {
            ProofStatus::WaitingForChallenge(proof) => proof.serialize_with_mode(writer, compress),
            ProofStatus::FinalProof(proof) => proof.serialize_with_mode(writer, compress),
        }
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        match self {
            ProofStatus::WaitingForChallenge(proof) => proof.serialized_size(compress),
            ProofStatus::FinalProof(proof) => proof.serialized_size(compress),
        }
    }
}

impl ActorMessage<Challenge> for Prover {
    type Reply = ProofStatus;

    async fn handle(
        &mut self,
        Challenge { point }: Challenge,
        _ctx: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        // TODO there's a better way to generate this
        self.point.push(point);
        let mut inputs: Vec<Option<Fq>> = self.point.iter().map(|&x| Some(x)).collect();
        inputs.push(None);

        if self.polynomial.num_vars == inputs.len() {
            ProofStatus::FinalProof(Proof(partial_eval(&self.polynomial, &inputs)))
        } else {
            ProofStatus::WaitingForChallenge(Proof(gen_uni_polynomial(&self.polynomial, &inputs)))
        }
    }
}

fn sum_poly(poly: &MultiPoly) -> Fq {
    (0..poly.num_vars)
        .map(|_| [Fq::zero(), Fq::one()])
        .multi_cartesian_product()
        .map(|x| poly.evaluate(&x))
        .fold(Fq::zero(), |acc, i| acc + i)
}

#[tokio::main]
async fn main() {
    // (1 - x1) * x2 * ((x3 + x4) - (x3 * x4))
    // Wow, why do we need to split that?
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

    use_interactive_sum_check(polynomial.clone(), h).await;
    use_fiat_shamir_sum_check(polynomial, h).await;
}

async fn use_interactive_sum_check(polynomial: MultiPoly, h: Fq) {
    let prover = Prover::new(polynomial.clone());
    let prover = kameo::spawn(prover);

    let random_generator = kameo::spawn(RandomGenerator);

    let verifier = Verifier::new(polynomial, h, random_generator.clone());
    let verifier = kameo::spawn(verifier);

    let mut proof = prover.ask(RequestProof).await.unwrap();
    loop {
        match verifier.ask(proof.proof()).await.unwrap() {
            VerificationStatus::Accept => {
                println!("Accepted!");
                break;
            }
            VerificationStatus::Reject(verification_error) => {
                println!("Error! {verification_error:?}");
                break;
            }
            VerificationStatus::Challenge(fp) => {
                proof = prover.ask(Challenge { point: fp }).await.unwrap();
            }
        }
    }
}

async fn use_fiat_shamir_sum_check(polynomial: MultiPoly, h: Fq) {
    let prover = Prover::new(polynomial.clone());
    let prover = kameo::spawn(prover);

    let proof = prover.ask(RequestProof).await.unwrap();

    let mut messages = Vec::new();
    let mut transcript = Transcript::default();

    transcript.append_transcript(&proof);
    messages.push(proof);

    // generate proof
    let mut is_final = false;
    while !is_final {
        let point = transcript.challenge();
        let message = prover.ask(Challenge { point }).await.unwrap();
        is_final = matches!(message, ProofStatus::FinalProof(_));
        transcript.append_transcript(&message);
        messages.push(message);
    }
    println!("[Main] Transcript: {:?}", messages);

    let random_generator = kameo::spawn(FiatShamirGenerator::default());

    let verifier = Verifier::new(polynomial, h, random_generator.clone());
    let verifier = kameo::spawn(verifier);

    for msg in messages {
        random_generator
            .tell(UpdateTranscript { msg: msg.clone() })
            .await
            .unwrap();

        match verifier.ask(msg.proof()).await.unwrap() {
            VerificationStatus::Accept => {
                println!("Accepted!");
                break;
            }
            VerificationStatus::Reject(verification_error) => {
                println!("Error! {verification_error:?}");
                break;
            }
            VerificationStatus::Challenge(_) => {}
        }
    }
}

#[cfg(test)]
mod test {
    use ark_std::One;

    use super::*;

    #[test]
    fn test_expand_polynomial() {
        let num_vars = 4;

        // Factor 1: (1 - x1)
        let terms = vec![
            (Fq::one(), SparseTerm::new(vec![])),
            (-Fq::one(), SparseTerm::new(vec![(0, 1)])),
        ];
        let poly1 = SparseMultilinearPolynomial::from_coefficients_vec(num_vars, terms);

        // Factor 2: x2

        let terms = vec![(Fq::one(), SparseTerm::new(vec![(1, 1)]))];
        let poly2 = SparseMultilinearPolynomial::from_coefficients_vec(num_vars, terms);

        // Factor 3: ( (x3 + x4) - (x3 * x4) )
        let terms = vec![
            (Fq::one(), SparseTerm::new(vec![(2, 1)])),
            (Fq::one(), SparseTerm::new(vec![(3, 1)])),
            (-Fq::one(), SparseTerm::new(vec![(2, 1), (3, 1)])),
        ];
        let poly3 = SparseMultilinearPolynomial::from_coefficients_vec(num_vars, terms);

        // Multiply the factors sequentially.
        // Multiplying poly1 and poly2 gives an intermediate result,
        // and then multiplying that result with poly3 expands the entire product.
        let poly_temp = naive_mul(&poly1, &poly2);
        let poly_expanded = naive_mul(&poly_temp, &poly3);

        // Print the expanded polynomial.
        println!("Expanded polynomial: {:?}", poly_expanded);

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

        println!("My test: {:?}", polynomial);
        assert_eq!(poly_expanded, polynomial)
    }

    fn naive_mul(cur: &MultiPoly, other: &MultiPoly) -> MultiPoly {
        if cur.is_zero() || other.is_zero() {
            MultiPoly::zero()
        } else {
            let mut result_terms = Vec::new();
            for (cur_coeff, cur_term) in &cur.terms {
                for (other_coeff, other_term) in &other.terms {
                    let mut term = cur_term.iter().cloned().collect::<Vec<_>>();
                    term.extend(other_term.iter().cloned());
                    result_terms.push((*cur_coeff * *other_coeff, SparseTerm::new(term)));
                }
            }
            MultiPoly::from_coefficients_slice(cur.num_vars, result_terms.as_slice())
        }
    }
}
