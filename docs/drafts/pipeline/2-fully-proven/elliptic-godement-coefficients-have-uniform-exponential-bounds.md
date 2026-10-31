# Elliptic Godement coefficients have uniform exponential bounds

- **Stage:** 2-fully-proven
- **Parent:** [Arithmetic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Every actual finite-field Weyl coefficient is bounded
  exponentially in inversion length throughout each fixed Godement chamber.
  Positive degree rotation makes the full Weyl series absolutely convergent.

## Proof

The actual adelic logarithmic height `H` is nonnegative. Hence
`|K_s(a)|≤|K_σ(a)|` whenever `Re(s)≥σ>1`. The
[audited global integral](../3-formalized/elliptic-radial-kernels-integrate-to-the-global-zeta-ratio.md)
and the integral norm inequality give
`|ζ_K(3^(-s))/ζ_K(3^(-s-1))|≤∫|K_σ|`. This is exactly
`arithmeticZetaRatio s`, since both spectral coordinates equal
`exp(-s log 3)`. Put `C_σ=1+∫|K_σ|≥1`.

For a Godement parameter, choose `σ` as the smaller simple-coroot real
part. Each positive coroot has argument with real part at least `σ`.
The product over the inversion set therefore has norm at most
`C_σ^length(w)≤exp(C_σ length(w))`.

For the translation and reflection families, the lengths are `|2m|` and
`|2m+1|`. The exact Cartan exponent has real part `c+b m-a m²`, with
`a>0` because the degree parameter and both simple-coroot real parts are
positive. Thus each complete summand has norm at most
`exp(c'+b'|m|-a m²)`.

Completing the square bounds this by
`exp(c'+(b'+1)²/(4a)) exp(-|m|)`. The latter is summable on the integers.
Adding the two dihedral families proves absolute convergence over the
entire affine Weyl group and identifies its sum with the two integer
series. Exponential chamber coordinates cover every parameter with both
simple-coroot real parts greater than one.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticWeylConvergence.lean`:
`norm_arithmeticZetaRatio_le_majorant`, `finiteFieldCoefficient_norm_le_exp`,
`summable_norm_finiteFieldWeylTerm`, and
`finiteFieldWeylSum_eq_two_series_chamber`. Direct audit pending.

This proves convergence of the independently defined Weyl side. Arithmetic
cell parametrization and equality with the Eisenstein constant term remain
obligations on the parent card.
