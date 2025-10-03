use crate::proof::*;
use crate::ssa::*;

use open_hypergraphs::lax::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum EvalErr {
    MultipleWrite(NodeId),
    MultipleRead(NodeId),
    ArityErr(EdgeId),
    C1(EdgeId),
    C2(EdgeId),
}

/// Evaluate a *closed* proof term, returning constructed rewrites.
pub fn eval<O: std::fmt::Debug + Clone + PartialEq, A: std::fmt::Debug + Clone + PartialEq>(
    proof: Proof<O, A>,
) -> Result<Vec<Rewrite<O, A>>, EvalErr> {
    assert_eq!(proof.sources.len(), 0, "proof term is not closed");

    let mut state = HashMap::<NodeId, Rewrite<O, A>>::new();
    let target_nodes = proof.targets.clone(); // needed because we call to_strict() shortly.

    let ssa = ssa(proof.to_strict()).unwrap();
    for op in ssa {
        // Read args to this op
        let mut args = vec![];
        for (node_id, _) in &op.sources {
            match state.remove(node_id) {
                Some(value) => args.push(value),
                None => return Err(EvalErr::MultipleRead(*node_id)),
            }
        }

        let results = apply(&op, args)?;

        for ((node_id, _), result) in op.targets.iter().zip(results) {
            if state.insert(*node_id, result).is_some() {
                return Err(EvalErr::MultipleWrite(*node_id));
            }
        }
    }

    // For each target node, try to read its value from the state, returning a MultipleRead error
    // if no value was present.
    println!("state: {:?}", state);
    target_nodes
        .iter()
        .map(|t| state.remove(t).ok_or(EvalErr::MultipleRead(*t)))
        .collect()
}

fn apply<O: Clone + PartialEq, A: Clone + PartialEq>(
    op: &SSA<Type, Cell<O, A>>,
    args: Vec<Rewrite<O, A>>,
) -> Result<Vec<Rewrite<O, A>>, EvalErr> {
    match &op.op {
        // n copies of input, for n ∈ ℕ
        Cell::Copy => {
            let [x] = get_exact_arity(1, &op, args)?;
            Ok(vec![x; op.targets.len()])
        }

        Cell::R(r) => {
            check_exact_coarity(1, &op)?;
            Ok(vec![r.clone()])
        }
        Cell::C0 => {
            check_exact_coarity(1, &op)?;
            let [a, b] = get_exact_arity(2, &op, args)?;
            Ok(vec![a.c0(&b)])
        }
        Cell::C1 => {
            check_exact_coarity(1, &op)?;
            let [a, b] = get_exact_arity(2, &op, args)?;
            let r = a.c1(b).ok_or(EvalErr::C1(op.edge_id))?;
            Ok(vec![r])
        }
        Cell::C2 => {
            check_exact_coarity(1, &op)?;
            let [a, b] = get_exact_arity(2, &op, args)?;
            let r = a.c2(b).ok_or(EvalErr::C2(op.edge_id))?;
            Ok(vec![r])
        }
    }
}

/// Make sure an op has exact arity m, consistent with arguments
fn get_exact_arity<const N: usize, O: Clone, A: Clone>(
    m: usize,
    op: &SSA<Type, Cell<O, A>>,
    args: Vec<Rewrite<O, A>>,
) -> Result<[Rewrite<O, A>; N], EvalErr> {
    if op.sources.len() != m {
        return Err(EvalErr::ArityErr(op.edge_id));
    }

    if args.len() != m {
        // TODO: return a better error here
        return Err(EvalErr::ArityErr(op.edge_id));
    }

    args.try_into().map_err(|_e| EvalErr::ArityErr(op.edge_id))
}

fn check_exact_coarity<O: Clone, A: Clone>(
    n: usize,
    op: &SSA<Type, Cell<O, A>>,
) -> Result<(), EvalErr> {
    if op.targets.len() != n {
        return Err(EvalErr::ArityErr(op.edge_id));
    }

    Ok(())
}
