# W4 — exact diagonal quadratic fibres

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Over every finite field of odd characteristic, a diagonal quadratic form with nonzero coefficients and determinant `D` has the following exact affine fibre counts:
  `N_(2k+1)(t)=q^(2k)+χ((-1)^k D t)q^k`,
  `N_(2k+2)(t)=q^(2k+1)+χ((-1)^(k+1)D)v(t)q^k`,
  where `v(0)=q−1` and `v(t)=−1` for `t≠0`.

## Proof

For `c≠0`, the bijection `(y,z)↦y−z` identifies `y²−z²=c` with the nonzero field elements; the inverse is `((u+c/u)/2,(c/u−u)/2)`. Counting square roots instead gives `Σ_y χ(y²−c)=−1`. At `c=0`, every nonzero square contributes one, giving `q−1`.

Scaling yields `Σ_y χ(t−ay²)=χ(−a)v(t)`. The square-root count also gives `Σ_y v(t−ay²)=qχ(at)`. Splitting off one coordinate in the actual solution set alternates these two identities. The one-dimensional square-root formula starts the induction. At zero, odd dimensions have count `q^(2k)`; even dimensions retain the signed-discriminant correction.

## Lean

[`DiagonalQuadricCounts.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/DiagonalQuadricCounts.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `squareDifferencePairs_card`, `quadraticChar_sum_sq_sub`: actual product-fibre count and character sum.
- `quadraticChar_sum_sub_mul_sq`, `quadraticZeroCorrection_sum_sub_mul_sq`: the two convolution identities.
- `diagonalQuadraticCount_succ`: exact coordinate-splitting recurrence.
- `diagonalQuadraticCount_odd`, `diagonalQuadraticCount_even`: complete affine distributions.
- `diagonalQuadraticCount_odd_zero`, `diagonalQuadraticCount_even_zero`: zero-fibre specializations.

Direct Lean check passed. These are classical finite-field quadratic counts, formalized as inputs to the [actual transverse quadric trace](../1-in-progress/w4-transverse-quadric-trace.md). Transport to the transverse form, projectivization, and its extension trace remain open.
