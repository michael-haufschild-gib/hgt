# W4 — the actual transverse quadratic determinant

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** At a normalized sign point `x` of `Σx_i=0` in `n=m+2` coordinates, the complete tangent chart is `v=(0,−Σw_j,w_0,…,w_(m−1))`. The reciprocal quadratic coefficient has matrix `diag(x_2,…,x_(m+1))+x_1 J` and determinant `−Π_i x_i`. With `r` negative coordinates, the determinant is `(-1)^(r+1)`.

## Proof

The first tangent coordinate is fixed at zero; the sum equation uniquely determines the second. Substitution into the reciprocal pairing gives the displayed matrix. The existing formal reciprocal series identifies this pairing's quadratic value with its second coefficient.

For square-one diagonal entries `d_i`, the diagonal rank-one determinant identity gives
`det(diag(d)+aJ)=(Πd_i)(1+aΣd_i)`. Indeed, each erased product is `d_iΠd_j`.
At the critical point, `1+x_1+Σd_i=0` and `x_1²=1`, so the final factor is `−x_1`.
The sign product is `(-1)^r`. The determinant is nonzero in every characteristic; the Hessian additionally has its factor of two.

## Lean

[`TransverseQuadraticForm.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/TransverseQuadraticForm.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `reciprocalTangentVector_reconstruct`, `reciprocalTangentVector_injective`: exhaustive, injective tangent chart.
- `reciprocalPairing_tangentVector_eq_matrix`, `reciprocalSeries_transverse_quadratic`: exact pairing and formal quadratic coefficient.
- `reciprocalTransverseMatrix_det`, `reciprocalTransverseMatrix_det_ne_zero`: determinant and nonsingularity.
- `reciprocalTransverseMatrix_det_critical`, `reciprocalTransverseMatrix_det_signs`: actual critical points and exact sign parity.

Direct Lean check passed. The [quadric point count and extension trace](../1-in-progress/w4-transverse-quadric-trace.md) remain open. No exceptional-divisor identification or global cohomological trace formula is asserted.
