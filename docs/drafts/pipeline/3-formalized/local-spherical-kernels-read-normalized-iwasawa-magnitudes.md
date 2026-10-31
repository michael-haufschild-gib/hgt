# Local spherical kernels read normalized Iwasawa magnitudes

- **Stage:** 3-formalized
- **Parent:** [Arithmetic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Actual finite and affine simple-root Iwasawa values give
  the normalized radial kernels. At a local completion their integrals are
  `(1-Q^(-z-1))/(1-Q^(-z))` for `Re(z)>0`; the actual normalized adelic
  sections integrate to the elliptic zeta ratio for `Re(z)>1`.

## Proof

The finite simple root has torus valuations `(1,M)` and the affine simple
root has `(M,M⁻¹)`, where `M=max(1,v(a))`. Residue normalization sends
`M` to `max(1,|a|_v)`. Writing `H_v=log(max(1,|a|_v))`, the section
exponents are `tH_v` and `(s-t)H_v`.

For an actual uniformizer, the shell of radius `n` has normalized magnitude
`Q^n`. The normalized spectral character on that shell is
`exp(-(z+1)n log Q)`. The audited shell integral gives the displayed local
factor and absolute convergence for `Re(z)>0`.

An idele has unit finite valuations outside a finite set. Its logarithmic
magnitude is therefore the sum of local logarithms, including infinity.
The actual adelic simple-root sections become `exp(tH)` and `exp((s-t)H)`.
Setting the indicated exponent to `-(z+1)H` identifies both with the actual
adelic radial kernel. Its global integral and absolute convergence give
the zeta ratio for `Re(z)>1`.

## Lean

The [local spectral integrals](actual-elliptic-local-spectral-characters-have-exact-integrals.md),
[actual simple-root valuations](actual-elliptic-simple-roots-have-exact-iwasawa-values.md),
and [actual simple-root section integrals](actual-elliptic-simple-root-integrals-are-zeta-ratios.md)
passed direct Lean and transitive axiom audits. Only `propext`,
`Classical.choice`, and `Quot.sound` occur.

Simple-intertwiner covariance and composition remain obligations of
arithmetic unfolding.
