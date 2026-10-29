# Absolutely convergent logarithmic Gaussian Gamma integrals

- **ID:** logarithmic-gaussian-mellin-integrals
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke archimedean Mellin integrals](../1-in-progress/hecke-archimedean-mellin-integrals.md)
- **Statement:** The logarithmic density `exp(2zu)*exp(-c*exp(2u))` is absolutely integrable for `c>0`, `Re z>0`, with integral `c^(-z)*Gamma(z)/2`; real and complex place specializations and finite-product integrals follow exactly.

## Dependency-closed proof

The existing exponential change of variables turns absolute Mellin convergence
into integrability of `exp(zu)*f(exp(u))`. Real dilation by two preserves
integrability, giving the exact equivalence for `t=exp(2u)`. The identity
`exp(u)*(exp(u))^(z-1)=exp(zu)` follows from the real logarithm of `exp(u)`.

Apply the equivalence to the actual positive-rate exponential. Its Mellin
convergence and Gamma value are the existing corpus results
`RHTower.mellinConvergent_exp_neg_mul` and
`RHTower.mellin_exp_neg_mul_finiteExponentialSumMellin`.
The already proved `RHTower.mellin_eq_integral_exp_two` supplies the factor two,
so the logarithmic integral is `c^(-z)*Gamma(z)/2`.

For a real place take `c=pi`, `z=(s+e)/2`, with `e` a natural parity exponent.
The value is `GammaR(s+e)/2`. For a complex place take `c=2*pi`, `z=s`;
Mathlib's definition `GammaC(s)=2*(2*pi)^(-s)*Gamma(s)` gives `GammaC(s)/4`.
Finite-product Fubini proves both absolute integrability and the exact product
of these scalar integrals. All rate and exponent conditions are explicit
natural domains of the generic theorem; the actual Hecke application must
prove them from its multiplicities and parities.

## Lean declarations and audit

Module: `GaloisForLFunctions/HTGeometry/LogarithmicGaussianMellin.lean`.

- `mellinConvergent_iff_integrable_exp_two`
- `logGaussianMellinKernel`
- `integrable_logGaussianMellinKernel`
- `integral_logGaussianMellinKernel`
- `integral_logGaussianMellinKernel_real`
- `integral_logGaussianMellinKernel_complex`
- `integrable_logGaussianMellinProduct`
- `integral_logGaussianMellinProduct`

Four main transitive axiom checks return only `propext`, `Classical.choice`,
and `Quot.sound`. Final source audit passed without warnings:

`lake --old env lean GaloisForLFunctions/HTGeometry/LogarithmicGaussianMellin.lean`

The module is wired into the geometry umbrella; no umbrella was compiled.
The actual Hecke-character product and its identification with the ideal
kernel remain on the active parent card.
