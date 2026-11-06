# W4 — the transverse quadric trace

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** Determine the finite-field projective zero count and extension trace of the actual transverse quadratic form at every normalized torus critical point.

## Exact algebraic target

The [transverse determinant](../3-formalized/w4-transverse-quadratic-determinant.md) is formalized. For `n≥2`, let `x_0=1`, every `x_i²=1`, and `Σx_i=0`. Eliminating a coordinate in the tangent space gives a diagonal-plus-rank-one matrix with determinant `−Π_i x_i`. With `r` negative coordinates, this is `(-1)^(r+1)`.

A concrete chart for `n=m+2` is `v=(0,−Σw_j,w_0,…,w_(m−1))`. Lean proves that it parametrizes the full tangent space and that `diag(x_2,…,x_(m+1))+x_1 J` represents exactly `reciprocalQuadratic x v` and the second coefficient of the reciprocal series.

The diagonal rank-one determinant formula reduces this to
`(Π_{i=1}^{n−2}x_i)(1+x_(n−1)Σ_{i=1}^{n−2}x_i)`.
The sum-zero and square-one equations make the second factor `−x_(n−1)`.

## Next geometric obligation

Prove the projective quadric count over every finite extension from this actual quadratic form. For even transverse dimension, its nonambient term depends on the quadratic character of the signed determinant; for odd transverse dimension, only the ambient projective terms remain. Do not identify this quadric with an exceptional divisor until an actual blow-up or local-model equivalence has been constructed.

For a nondegenerate diagonal form with determinant `D` over an odd finite field, the exact affine targets are
`N_(2k+1)(t)=q^(2k)+χ((-1)^k D t)q^k` and
`N_(2k+2)(t)=q^(2k+1)+χ((-1)^(k+1)D)v(t)q^k`,
where `v(0)=q−1` and `v(t)=−1` for `t≠0`.
Both affine distributions and their actual-set recurrence are [formalized](../3-formalized/w4-diagonal-quadric-counts.md). The elementary input is `Σ_y χ(y²−c)=v(c)`: count `y²−z²=c` through the bijection `(y,z)↔(y−z,y+z)`. For `c≠0`, the product equation has `q−1` points. Induction on a diagonal variable gives the displayed distributions.

Removing the zero vector and quotienting by nonzero scalars gives the projective trace. In transverse dimension `2k+2`, it is `Σ_{j=0}^{2k}q^j+χ((-1)^(k+1)D)q^k`; in dimension `2k+1`, it is `Σ_{j=0}^{2k−1}q^j`. The even-dimensional formula requires proving how the quadratic character changes under finite extension.

For the actual critical form, `D` is a sign. The inspected identity `quadraticChar_neg_one` expresses its character through `χ₄(q)`. Multiplicativity and `#E=q^[E:F]` should therefore give the extension law directly: the nonambient eigenvalue is `χ_F((-1)^(k+1)D)q^k`. No general character-norm formula is needed for this specialization.

## Available inputs

- `reciprocalSeries_quadratic` and `reciprocalPairing_transverse_nondegenerate` identify the exact quadratic coefficient and its radical.
- `HTGeometry.bgv_det_diagonal_add_vecMulVec` proves the determinant identity over arbitrary commutative rings.
- `diagonalQuadraticCount_odd` and `diagonalQuadraticCount_even` prove the complete affine distributions. Transport to the actual transverse matrix and its projective quotient remain to be constructed.

This supplies a local spectral correction, not the compactification's missing global trace formula or the ζ family.
