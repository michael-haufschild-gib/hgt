# Strict-prefix sampling preserves finite product Haar

- **Stage:** 3-formalized
- **Parent:** [Triangular root coefficients](../1-in-progress/triangular-root-coefficients-unfold-arithmetic-cells.md).
- **Statement:** If `f:(C,μ)→(G,ν)` preserves sigma-finite measures and `ν`
  is translation invariant, then `x_i↦f(x_i)+φ_i(x_{<i})` preserves every
  finite product measure for measurable strict-prefix corrections `φ_i`.

## Proof

Induct on the number of coordinates. The empty product is immediate.
Split the successor product into its prefix and last coordinate. The
induction hypothesis preserves the prefix law. For each fixed prefix,
the last map is the scalar sampler followed by a translation, so it
preserves the last Haar law. Measurability and the skew-product theorem
preserve the product law. The measurable head-last equivalences return
the original coordinate order.

## Lean

`HTGeometry/LoopEisenstein/TriangularSampling.lean`:
`measurePreserving_finiteTriangularSampling`. Direct Lean audit passed;
the declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
