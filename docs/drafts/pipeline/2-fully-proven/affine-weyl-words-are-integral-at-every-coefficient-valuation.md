# Affine Weyl words are integral at every coefficient valuation

- **Stage:** 2-fully-proven
- **Parent:** [Arithmetic cell coordinates](../1-in-progress/affine-a1-bruhat-cells-have-one-polynomial-root-coordinate.md).
- **Statement:** Every affine Weyl matrix has an actual central-loop lift
  integral for every coefficient valuation.

## Proof

The finite simple embedding of `W(1)` projects to `W(1)`; the affine
simple embedding of `W(-1)` projects to `W(X)`. Both source matrices have
entries in `{0,1,-1}`, so both words lie in the coefficient-integral
simple-loop subgroup for every valuation.

Their quotient projects to `D(X⁻¹)`. Its integer powers give all translation
matrices; multiplying them by the finite Weyl word gives the reflection
matrices. Subgroup closure preserves integrality. These are explicit words;
no identification of their central coordinates with another lift is required.

## Lean

`HTGeometry/LoopEisenstein/IntegralWeylWords.lean`:
`LoopSL2.projection_integralWeylWord` and
`LoopSL2.integralWeylWord_mem_integralLoop`. Direct audit pending.
