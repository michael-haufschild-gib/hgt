# W4 — the coordinate boundary of the reciprocal locus

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Let `E(x)=Σ_i Π_{j≠i}x_j`. On the projective intersection `Σx_i=E(x)=0`, no point has exactly one zero coordinate. At a point with exactly two zero coordinates `a,b`, the linear coefficient of `E(x+tv)` is `(v_a+v_b)Π_{j≠a,b}x_j`; its restriction to `Σv_i=0` is nonzero. At a point with at least three zero coordinates, the whole linear coefficient vanishes.

## Proof mechanism

Every monomial of `E` omits exactly one coordinate. One zero leaves one nonzero monomial. Two zeros require the line expansion to replace one of those zeros, leaving precisely two linear terms. Three zeros leave at least two zero factors in every monomial, so no linear term survives. For two zeros and a nonzero coordinate `c`, use `v=e_a−e_c` to test the sum-zero tangent hyperplane.

On the torus there is an exact formal-series identity `E(x+tv)=Π_i(x_i+tv_i)·Σ_i(x_i+tv_i)⁻¹`. At a reciprocal zero its linear coefficient is `Π_i x_i` times the reciprocal differential. Thus clearing denominators preserves the torus critical locus; the new critical strata occur on the coordinate boundary.

## Role

This separates the finite torus critical locus from coordinate strata in the projective compactification. Resolution, the cohomological trace formula, and the weight bound remain open; first-order classification alone proves none of them.

## Lean

[`ReciprocalProjectiveBoundary.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/ReciprocalProjectiveBoundary.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `reciprocalClearedSeries_eq`, `reciprocalCleared_torus_critical_iff`: exact denominator clearing and preservation of the torus critical locus.
- `reciprocalClearedValue_ne_zero_of_one_zero`: exclusion of one-zero points.
- `reciprocalClearedSeries_linear_of_two_zeros`, `reciprocalClearedSeries_transverse_of_two_zeros`: exact linear term and a nonzero sum-zero tangent test.
- `reciprocalClearedSeries_linear_of_three_zeros`: vanishing of every linear term.
- `reciprocalBoundary_critical_iff`: at a nonzero boundary point of the cleared zero locus, differential rank drops on the sum-zero hyperplane exactly when at least three coordinates vanish.

Direct Lean check passed.
