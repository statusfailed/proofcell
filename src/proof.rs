use open_hypergraphs::lax::var::HasVar;
use open_hypergraphs::lax::*;

// The objects of our category are *types* of the underlying category.
// NOTE: this introduces some data hierarchy that will have to be dealt with.
//pub struct Type<O> {
//source: Vec<O>,
//target: Vec<O>,
//}

#[derive(Debug, Clone, PartialEq)]
pub struct Type;

/// A single rewrite rule over the monoidal signature `Σ = (O, A)`.
#[derive(Debug, Clone, PartialEq)]
pub struct Rewrite<O, A> {
    source: OpenHypergraph<O, A>,
    target: OpenHypergraph<O, A>,
}

impl<O: Clone + PartialEq, A: Clone + PartialEq> Rewrite<O, A> {
    pub fn new(source: OpenHypergraph<O, A>, target: OpenHypergraph<O, A>) -> Option<Self> {
        if (source.source() != target.source()) || (source.target() != target.target()) {
            None
        } else {
            Some(Rewrite { source, target })
        }
    }

    pub fn source(&self) -> &OpenHypergraph<O, A> {
        &self.source
    }

    pub fn target(&self) -> &OpenHypergraph<O, A> {
        &self.target
    }

    pub fn into_parts(self) -> (OpenHypergraph<O, A>, OpenHypergraph<O, A>) {
        (self.source, self.target)
    }
}

impl<O: Clone + PartialEq, A: Clone + PartialEq> Rewrite<O, A> {
    pub fn c0(&self, other: &Self) -> Self {
        let source = &self.source | &other.source;
        let target = &self.target | &other.target;
        Rewrite::new(source, target).unwrap() // should never fail if self, other were valid
    }

    pub fn c1(self, other: Self) -> Option<Self> {
        let source = (&self.source >> &other.source)?;
        let target = (&self.target >> &other.target)?;
        Rewrite::new(source, target)
    }

    pub fn c2(self, other: Self) -> Option<Self> {
        // TODO: this needs proper hypergraph isomorphism checking!
        if self.target != other.source {
            return None;
        }

        Rewrite::new(self.source, other.target)
    }
}

/// A Cell is a generator of a proof term.
#[derive(Debug, Clone, PartialEq)]
pub enum Cell<O, A> {
    Copy,             // Reuse or discard a rewrite
    R(Rewrite<O, A>), // A rewrite `r : f → g`
    C0,               // Pointwise monoidal product
    C1,               // Pointwise composition
    C2,               // Composition of rewrites
}

impl<O, A> Cell<O, A> {
    pub fn profile(&self) -> (usize, usize) {
        use Cell::*;
        match self {
            Copy => (1, 2),
            R(_) => (0, 1),
            C0 | C1 | C2 => (2, 1),
        }
    }

    pub fn proof(self) -> Proof<O, A> {
        let (m, n) = self.profile();
        let s = vec![Type; m];
        let t = vec![Type; n];
        OpenHypergraph::singleton(self, s, t)
    }
}

/// A proof term: a derivation of a rewrite (or multiple rewrites) by pasting of cells
pub type Proof<O, A> = OpenHypergraph<Type, Cell<O, A>>;

impl<O, A> HasVar for Cell<O, A> {
    fn var() -> Self {
        Self::Copy
    }
}

/// An axiom is a rewrite which is assumed.
/// Diagrammatically, it's a constant R with no inputs and one output (the rewrite)
pub fn axiom<O, A>(r: Rewrite<O, A>) -> Proof<O, A> {
    Cell::R(r).proof()
}
