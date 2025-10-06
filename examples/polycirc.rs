//! # Polynomial Circuits
use std::fmt::Display;

use open_hypergraphs::category::*;
use open_hypergraphs::lax::OpenHypergraph;

use proofcell::svg;
use proofcell::*;

////////////////////////////////////////////////////////////////////////////////
// Define the theory of polynomial circuits

/// There is a single generating object in the category; thought of as a primitive type (like "Int"
/// or "Real".
#[derive(Clone, PartialEq, Eq, Debug, Copy)]
pub struct Obj;

impl Display for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Obj")
    }
}

/// Generating arrows are basic arithmetic operations with copying and discarding.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Arr {
    Copy,
    Discard,
    Add,
    Zero,
    Mul,
    One,
    Neg,
}

impl Display for Arr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Arr::Copy => write!(f, "Δ"),
            Arr::Discard => write!(f, "!"),
            Arr::Add => write!(f, "+"),
            Arr::Zero => write!(f, "0"),
            Arr::Mul => write!(f, "×"),
            Arr::One => write!(f, "1"),
            Arr::Neg => write!(f, "-"),
        }
    }
}

impl Arr {
    // Arity and coarity
    pub fn profile(&self) -> (usize, usize) {
        use Arr::*;
        match self {
            Copy => (1, 2),
            Discard => (1, 0),
            Add | Mul => (2, 1),
            Zero | One => (0, 1),
            Neg => (1, 1),
        }
    }

    // map a generator to a term
    pub fn term(&self) -> Term {
        let (m, n) = self.profile();
        let s = vec![Obj; m];
        let t = vec![Obj; n];
        OpenHypergraph::singleton(self.clone(), s, t)
    }
}

impl From<Arr> for OpenHypergraph<Obj, Arr> {
    fn from(value: Arr) -> Self {
        value.term()
    }
}

pub type Term = OpenHypergraph<Obj, Arr>;

////////////////////////////////////////////////////////////////////////////////
// Example terms

// helper for quotienting
fn q(mut t: Term) -> Term {
    t.quotient();
    t
}

fn id() -> Term {
    OpenHypergraph::identity(vec![Obj])
}

fn sub() -> Term {
    (&(&id() | &Arr::Neg.into()) >> &Arr::Add.into()).unwrap()
}

fn self_difference() -> Term {
    (&Arr::Copy.into() >> &sub()).unwrap()
}

// n-wire zero morphism
fn zero() -> Term {
    (&Arr::Discard.term() >> &Arr::Zero.term()).unwrap()
}

fn mul_zero() -> Term {
    let id_zero = &id() | &Arr::Zero.term();
    (&id_zero >> &Arr::Mul.term()).unwrap()
}

fn mul_one() -> Term {
    let id_one = &id() | &Arr::One.term();
    (&id_one >> &Arr::Mul.term()).unwrap()
}

////////////////////////////////////////////////////////////////////////////////
// Some axioms

// x - x ~> 0
fn self_difference_is_zero() -> Rewrite<Obj, Arr> {
    Rewrite::new(self_difference(), zero()).unwrap()
}

// 0 ~> x*0
fn zero_is_annihilation() -> Rewrite<Obj, Arr> {
    Rewrite::new(zero(), mul_zero()).unwrap()
}

fn mul_id() -> Rewrite<Obj, Arr> {
    Rewrite::new(mul_one(), id()).unwrap()
}

////////////////////////////////////////////////////////////////////////////////
// Proofs

/// Proof that 1x + (-1x) = 0x
fn mul_id_self_difference_is_annihilation() -> Proof<Obj, Arr> {
    let a =
        &axiom(self_difference_is_zero()) | &(&axiom(zero_is_annihilation()) | &axiom(mul_id()));
    let b = &Cell::C2.proof() | &OpenHypergraph::identity(vec![proof::Type]);
    let mut proof = (&(&a >> &b).unwrap() >> &Cell::C1.proof()).unwrap();
    proof.quotient();
    proof
}

pub fn main() {
    let proof = mul_id_self_difference_is_annihilation();

    // save svg
    let display = proof
        .clone()
        .map_edges(|e| format!("{}", e.name()))
        .map_nodes(|_n| format!(""));
    svg::save_svg(&display, "proof.svg".as_ref()).unwrap();

    let rewrite = eval(proof).expect("eval error").pop().unwrap();
    let (source, target) = rewrite.into_parts();
    svg::save_svg(&q(source), "rw0.svg".as_ref()).unwrap();
    svg::save_svg(&q(target), "rw1.svg".as_ref()).unwrap();
}
