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

The [discriminant transport](../3-formalized/w4-quadratic-fibres-from-discriminants.md) is formalized: diagonalization preserves every actual fibre count, and the discriminant changes by the square of an invertible coordinate determinant. Consequently `symmetricMatrix_quadraticCount_odd` and `symmetricMatrix_quadraticCount_even` give these distributions for every nonsingular symmetric matrix. Applying them to the reciprocal matrix remains to be wired.

The [actual projective quotient count](../3-formalized/w4-projective-quadric-counts.md) is formalized for every nondegenerate quadratic form. Each point has exactly `q−1` nonzero representatives. In vector dimension `2k+2`, the count is `Σ_{j=0}^{2k}q^j+χ((-1)^(k+1)D)q^k`; in dimension `2k+1`, it is `Σ_{j=0}^{2k−1}q^j`. The reciprocal transverse specialization and its finite-extension trace remain unproved.

**Unproved continuation:** for the actual critical form, `D` is a sign. The identity `quadraticChar_neg_one` expresses its character through `χ₄(q)`. Multiplicativity and `#E=q^[E:F]` suggest the extension law with nonambient eigenvalue `χ_F((-1)^(k+1)D)q^k`. Neither this extension law nor its identification with the reciprocal projective count is asserted as a completed proof.

## Available inputs

- `reciprocalSeries_quadratic` and `reciprocalPairing_transverse_nondegenerate` identify the exact quadratic coefficient and its radical.
- `HTGeometry.bgv_det_diagonal_add_vecMulVec` proves the determinant identity over arbitrary commutative rings.
- `diagonalQuadraticCount_odd`, `diagonalQuadraticCount_even`, `quadraticFormCount_odd`, and `quadraticFormCount_even` prove the complete affine distributions.
- `projectiveQuadric_card_odd` and `projectiveQuadric_card_even` prove the actual scalar-quotient counts. Their specialization to the reciprocal transverse form remains open.

The intended local correction would still leave the compactification's global trace formula and the ζ family open.
