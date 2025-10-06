# Proofcell

A proof kernel for symmetric monoidal theories.

# Examples

Two examples can be run:

    cargo run --example <polycirc|dfol>

Both will produce a proof whose output is a single computed rewrite rule; itself a pair of maps.
Running the example saves three diagrams:

- `proof.svg`: a diagrammatic representation of the proof term, with some detail omitted
- `rw0.svg`: the *source* of the output rewrite
- `rw1.svg`: the *target* of the output rewrite

The `dfol` example encodes the "wrong-way" theorem from [https://arxiv.org/pdf/2401.07055],
while `polycirc` encodes a proof of `1x + (-1x) = 0x`.
