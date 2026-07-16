# Finite matrix spectral moments and block-Hankel capacity

- **ID:** `finite-matrix-spectral-block-hankel`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, coupled-channel spectral positivity and rank
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FiniteMatrixSpectralHankel`

## Matrix-valued spectral law

For `d` common spectral lines and `m` field/reporter channels, define

```text
M_k(a,b) = sum_(r<d) mass_r coupling_r(a) coupling_r(b) node_r^k.     (1)
```

The order-`n` block Hankel matrix is indexed by `(i,a),(j,b)` and has entry
`M_(i+j)(a,b)`.  For nonnegative masses it is exactly the Gram matrix of features

```text
v_(i,a)(r) = sqrt(mass_r) coupling_r(a) node_r^i.                     (2)
```

Therefore every block is positive semidefinite.  It is positive definite, equivalently has
nonzero determinant, exactly when the complete joint clock-channel feature family `(2)` is
linearly independent.

## Positive capacity statement

The common spectral palette remains the actual information budget.  If

```text
d < n*m,
```

then the `n*m` joint features lie in a `d`-dimensional spectral space and the block determinant
vanishes.  Additional channels help only when their couplings add independent feature directions;
they do not manufacture new spectral lines.

Conversely, joint feature independence gives a strictly positive block determinant.  This is an
exact multi-field identifiability criterion, not merely a finite-spectrum no-go.

## Scalarization and direct corpus application

Contract both channel indices with a reporter vector `u`.  The effective coupling at line `r` is

```text
c_eff(r) = sum_a u_a coupling_r(a),
```

and the scalarized moment is exactly

```text
u^T M_k u = sum_r mass_r c_eff(r)^2 node_r^k.                         (3)
```

Thus every scalar reporter of the matrix spectrum has `SpectralWidthAtMost d`.  Equation `(3)`
directly discharges the representation hypothesis of the existing scalar finite-spectral Hankel
theorems, yielding

```text
det H_(d+1)(u^T M u) = 0.                                            (4)
```

This applies the new matrix structure to the rest of the Lean corpus rather than leaving it as an
isolated definition.

## Physics scope

The same finite algebra occurs in:

- multi-field EFT scattering and positivity bounds for scalar, vector, fermion, and graviton
  sectors;
- coupled strong/weak/electromagnetic/Higgs current correlators;
- lattice-QCD variational correlation matrices and matrix spectral reconstruction;
- multi-detector gravitational-wave or neutron-star mode spectroscopy;
- multi-output system identification and learned spectral models.

Primary literature:

- S.-L. Wan and S.-Y. Zhou, *Matrix moment approach to positivity bounds and UV reconstruction
  from IR*, arXiv:2411.11964.
- X. Li, H. Xu, C. Yang, C. Zhang, and S.-Y. Zhou, *Positivity in Multi-Field EFTs*,
  arXiv:2101.01191.
- Z.-Z. Du, C. Zhang, and S.-Y. Zhou, *Triple crossing positivity bounds for multi-field
  theories*, arXiv:2111.01169.
- R. Abbott, W. I. Jay, and P. R. Oare, *Moment problems and bounds for matrix-valued smeared
  spectral functions*, arXiv:2508.01377.

## Lean surface

- `finiteMatrixSpectralMoment`
- `finiteMatrixSpectralBlockHankel`
- `finiteMatrixSpectralFeature`
- `finiteMatrixSpectralBlockHankel_eq_gram`
- `finiteMatrixSpectralBlockHankel_posSemidef`
- `finiteMatrixSpectralBlockHankel_posDef_iff_linearIndependent`
- `det_finiteMatrixSpectralBlockHankel_ne_zero_iff_linearIndependent`
- `det_finiteMatrixSpectralBlockHankel_pos_of_linearIndependent`
- `det_finiteMatrixSpectralBlockHankel_eq_zero_of_spectralLines_lt`
- `finiteMatrixSpectralEffectiveCoupling`
- `finiteMatrixSpectralScalarizedMoment`
- `finiteMatrixSpectralScalarizedMoment_eq_finiteSpectralMoment`
- `finiteMatrixSpectralScalarizedMoment_spectralWidthAtMost`
- `det_momentHankelMatrix_finiteMatrixSpectralScalarizedMoment_succ_eq_zero`

## RH impact and boundary

This expands the QFT/EFT source language from scalar to coupled-channel moments and can expose
positive scalar contractions or independent feature blocks that are invisible in one field.  Any
matrix-valued prime--Gamma spectral construction would immediately yield the existing scalar
moment interfaces after contraction.

No such source-defined matrix spectral representation is constructed here, so the result does not
prove RH.  Its concrete contribution is a stronger representation class, exact positivity/rank
laws, and automatic reduction to the already formalized scalar consumers.

## Verification

- [x] exact module target built and cached
- [x] touched file checks directly
- [x] no numerical computation used
