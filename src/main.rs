use ark_ff::{Field, One, UniformRand, Zero};
use ark_poly::{
    multivariate::{SparsePolynomial as SparseMultilinearPolynomial, SparseTerm, Term},
    univariate::DensePolynomial as UniPoly,
    DenseMVPolynomial, DenseUVPolynomial, Polynomial,
};
use itertools::Itertools;
use kameo::{
    actor::ActorRef,
    message::{Context, Message as ActorMessage},
    Actor, Reply,
};

mod polynomial;
mod scalar;

use scalar::Fq;

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
struct Verifier {
    polynomial: MultiPoly,
    last_val: Fq,
    oracle: ActorRef<Oracle>,
    point: Vec<Fq>,
}

impl Verifier {
    pub fn new(polynomial: MultiPoly, h: Fq, oracle: ActorRef<Oracle>) -> Self {
        Self {
            last_val: h,
            oracle,
            polynomial,
            point: vec![],
        }
    }
}

#[derive(Reply)]
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

impl ActorMessage<Proof> for Verifier {
    type Reply = VerificationStatus;

    async fn handle(
        &mut self,
        Proof(polynomial_g): Proof,
        _ctx: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        // We don't need to check for variables because the typesystem assure it's only 1 variable

        // TODO maybe I need to check the degree of the variable instead of degree of the
        // polynomial
        if polynomial_g.degree() > self.polynomial.degree() {
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

        let random_point = {
            let mut rng = ark_std::rand::thread_rng();
            // return a challenge
            Fq::rand(&mut rng)
        };

        println!("[Verifier] Random point = {}", random_point);
        self.last_val = polynomial_g.evaluate(&random_point);
        self.point.push(random_point);
        println!(
            "[Verifier] Polynomial evaluated at random point = {}",
            self.last_val
        );
        println!("[Verifier] Point[] = {:?}", self.point);
        if self.point.len() == self.polynomial.num_vars() {
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
    type Reply = Proof;

    async fn handle(
        &mut self,
        _msg: RequestProof,
        _ctx: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        let polynomial = gen_uni_polynomial(&self.polynomial, &[None]);
        Proof(polynomial)
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

impl ActorMessage<Challenge> for Prover {
    type Reply = Proof;

    async fn handle(
        &mut self,
        Challenge { point }: Challenge,
        _ctx: Context<'_, Self, Self::Reply>,
    ) -> Self::Reply {
        self.point.push(point);
        let mut inputs: Vec<Option<Fq>> = self.point.iter().map(|&x| Some(x)).collect();
        inputs.push(None);
        let max_rounds = self.polynomial.num_vars;
        let polynomial = match inputs.len() {
            i if i == max_rounds => partial_eval(&self.polynomial, &inputs),
            _ => gen_uni_polynomial(&self.polynomial, &inputs),
        };

        Proof(polynomial)
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

    let prover = Prover::new(polynomial.clone());

    let prover = kameo::spawn(prover);
    let oracle = Oracle::new(polynomial.clone());
    let oracle = kameo::spawn(oracle);
    let verifier = Verifier::new(polynomial, h, oracle);
    let verifier = kameo::spawn(verifier);
    let mut proof = prover.ask(RequestProof).await.unwrap();
    loop {
        match verifier.ask(proof).await.unwrap() {
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
