# W4 — exact projective quadratic zero loci

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For a nondegenerate quadratic form over an odd finite field, with discriminant `D`, the actual scalar quotient of its nonzero zeros has cardinality
  `Σ_{j=0}^{2k−1}q^j` in vector dimension `2k+1`, and
  `Σ_{j=0}^{2k}q^j+χ((-1)^(k+1)D)q^k` in vector dimension `2k+2`.
  The first sum is empty when `k=0`.

## Proof

Homogeneity preserves the nonzero zero locus under every nonzero scalar. For each projective point, choose a representative. Scaling it gives a bijection from the nonzero field elements to its fibre: surjectivity is scalar equivalence, and injectivity follows by cancellation in a nonzero coordinate.

Thus `#cone=(q−1)#projective`. Removing the origin from the affine zero fibre gives
`(q−1)#projective=N(0)−1`, including dimension zero. Substitute the [affine discriminant formulas](w4-quadratic-fibres-from-discriminants.md) and use
`(q−1)Σ_{j=0}^{r−1}q^j=q^r−1`. Since `q>1`, cancellation gives the stated projective counts.

## Lean

[`ProjectiveQuadricCounts.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/ProjectiveQuadricCounts.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `ProjectiveQuadric`: actual scalar quotient of the nonzero quadratic zero locus.
- `projectiveQuadricFiberEquiv`: bijection between a quotient fibre and nonzero scalars.
- `quadraticCone_card_orbits`, `projectiveQuadric_card_mul`: exact affine-to-projective count.
- `projectiveQuadric_card_odd`, `projectiveQuadric_card_even`: the two discriminant formulas.

Direct Lean check passed. The reciprocal transverse specialization, its finite-extension trace, and any exceptional-divisor identification remain unproved. These are classical projective-quadric counts, formalized for that application.
