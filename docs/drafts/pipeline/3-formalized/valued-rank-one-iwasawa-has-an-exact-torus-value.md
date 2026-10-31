# Valued rank-one Iwasawa decomposition has an exact torus value

- **Stage:** 3-formalized
- **Parent:** [Integral loop vertices](../1-in-progress/valued-loop-iwasawa-and-integral-vertices.md).
- **Statement:** Over a field with valuation `v:F→ℤᵐ⁰`, every
  `g∈SL₂(F)` factors as `bk`, where `b` is upper triangular and all
  entries of `k` are integral. Every such factorization satisfies
  `v(b₂₂)=max(v(g₂₁),v(g₂₂))`.

## Proof

Write the bottom row as `(c,d)`. If `v(c)≤v(d)`, then `d≠0` and
  `k=[[1,0],[c/d,1]]` is integral. Otherwise `c≠0` and use
  `k=[[0,−1],[1,d/c]]`. In both cases direct multiplication makes
  `gk⁻¹` upper triangular and gives the asserted lower diagonal value.

The adjugate of an integral determinant-one matrix is integral. The
ultrametric inequality bounds the maximum bottom-row value after right
multiplication by such a matrix. Applying the same bound to its inverse
gives equality. This proves independence of the factorization.
For an integral triangular matrix, the two diagonal values are at most
one and their product is one; hence each equals one.

## Lean

`HTGeometry/LoopEisenstein/ValuedSL2Iwasawa.lean`:
`exists_valued_sl2_upper_integral`, `valued_sl2_bottomRow_mul_integral`,
`valued_sl2_iwasawa_torus_value`, `valued_sl2_triangular_diagonal_value`.
Direct Lean check passed. All four capstones use exactly `propext`,
`Classical.choice`, `Quot.sound`.
