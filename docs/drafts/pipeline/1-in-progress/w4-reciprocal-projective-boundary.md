# W4 — the coordinate boundary of the reciprocal locus

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Let `E(x)=Σ_i Π_{j≠i}x_j`. On the projective intersection `Σx_i=E(x)=0`, no point has exactly one zero coordinate. At a point with exactly two zero coordinates `a,b`, the linear coefficient of `E(x+tv)` is `(v_a+v_b)Π_{j≠a,b}x_j`; its restriction to `Σv_i=0` is nonzero. At a point with at least three zero coordinates, the whole linear coefficient vanishes.

## Proof mechanism

Every monomial of `E` omits exactly one coordinate. One zero leaves one nonzero monomial. Two zeros require the line expansion to replace one of those zeros, leaving precisely two linear terms. Three zeros leave at least two zero factors in every monomial, so no linear term survives. For two zeros and a nonzero coordinate `c`, use `v=e_a−e_c` to test the sum-zero tangent hyperplane.

## Role

This separates the finite torus critical locus from coordinate strata in the projective compactification. Resolution, the cohomological trace formula, and the weight bound remain open; first-order classification alone proves none of them.
