use open_hypergraphs::lax::*;
use proofcell::*;

////////////////////////////////////////////////////////////////////////////////
// Basic theory (diagrammatic first order logic)

// Diagrammatic first-order logic terms are over some *signature* A, consisting of a set of
// `m → n` relation symbols.
pub type Term<A> = OpenHypergraph<Obj, Arr<A>>;

// Single-sorted (TODO: black/white typed wires instead?)
#[derive(Clone, PartialEq, Debug)]
pub struct Obj;

impl std::fmt::Display for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "()")
    }
}

// generators (R) are white or black
// contexts are white or black
#[derive(Clone, PartialEq, Debug)]
pub enum Arr<A> {
    // White generators
    WG(A),
    // Black generators
    BG(A),
    // Contexts
    WC(Term<A>),
    BC(Term<A>),
}

impl<A: std::fmt::Debug> std::fmt::Display for Arr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

////////////////////////////////////////////////////////////////////////////////
// Example terms

fn ff(x: Vec<usize>, n: usize) -> open_hypergraphs::strict::vec::FiniteFunction {
    use open_hypergraphs::strict::vec::*;
    println!("{x:?} {n}");
    FiniteFunction::new(VecArray(x), n).expect("oh no")
}

fn unit<A: Clone + PartialEq>() -> Term<A> {
    OpenHypergraph::spider(ff(vec![], 1), ff(vec![0], 1), vec![Obj]).unwrap()
}

fn split<A: Clone + PartialEq>() -> Term<A> {
    OpenHypergraph::spider(ff(vec![0], 1), ff(vec![0, 0], 1), vec![Obj]).unwrap()
}

fn join<A: Clone + PartialEq>() -> Term<A> {
    OpenHypergraph::spider(ff(vec![0, 0], 1), ff(vec![0], 1), vec![Obj]).unwrap()
}

fn cup<A: Clone + PartialEq>() -> Term<A> {
    (&unit() >> &split()).unwrap()
}

fn id<A: Clone + PartialEq>() -> Term<A> {
    OpenHypergraph::identity(vec![Obj])
}

////////////////////////////////////////////////////////////////////////////////
// Axioms

// TODO: this is an axiom *schema*, but currently lives at the meta-level (Rust).
fn nat<A: Clone + PartialEq>(r: &Term<A>) -> Rewrite<Obj, Arr<A>> {
    let j = join();
    let source = (&j >> r).unwrap();
    let target = (&(r | r) >> &j).unwrap();
    Rewrite::new(source, target).unwrap()
}

////////////////////////////////////////////////////////////////////////////////
// Proofs

/// The "wrong-way" lemma
/// NOTE: this takes an identity rewrite (r : 1 → 1) to properly become an axiom *schema*.
fn wrong_way<A: Clone + PartialEq>(r: &Term<A>) -> Proof<Obj, Arr<A>> {
    let ax_cup = axiom(Rewrite::identity(cup::<A>()));
    let ax_id = axiom(Rewrite::identity(id::<A>()));
    let ax_nat = axiom(nat(r));

    let lhs = &(&(&ax_cup | &ax_id) | &ax_id) | &ax_nat;
    let mid = &Cell::C0.proof() | &Cell::C0.proof();
    let rhs = Cell::C1.proof();

    (&(&lhs >> &mid).unwrap() >> &rhs).unwrap()
}

////////////////////////////////////////////////////////////////////////////////
// Example of wrong-way with concrete signature `Sym`, encoding a set of symbols.

#[derive(Clone, PartialEq, Debug)]
pub enum Sym {
    R,
}

impl Sym {
    pub fn into_white(self) -> Term<Sym> {
        OpenHypergraph::singleton(Arr::WG(self), vec![Obj], vec![Obj])
    }

    pub fn into_black(self) -> Term<Sym> {
        OpenHypergraph::singleton(Arr::BG(self), vec![Obj], vec![Obj])
    }
}

impl std::fmt::Display for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "R")
    }
}

fn q<A: Clone>(mut t: Term<A>) -> Term<A> {
    t.quotient();
    t
}

pub fn main() {
    let mut proof = wrong_way(&Sym::R.into_white());
    proof.quotient();

    // save svg
    let display = proof
        .clone()
        .map_edges(|e| format!("{}", e.name()))
        .map_nodes(|_| format!(""));
    svg::save_svg(&display, "proof.svg".as_ref()).unwrap();

    let rewrite = eval(proof).expect("eval error").pop().unwrap();
    let (source, target) = rewrite.into_parts();
    svg::save_svg(&q(source), "rw0.svg".as_ref()).unwrap();
    svg::save_svg(&q(target), "rw1.svg".as_ref()).unwrap();
}
