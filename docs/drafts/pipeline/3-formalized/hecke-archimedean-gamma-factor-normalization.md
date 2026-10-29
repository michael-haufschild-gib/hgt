# Actual Hecke Gamma factors and radial normalization

- **ID:** hecke-archimedean-gamma-factor-normalization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Archimedean Mellin integrals](hecke-archimedean-mellin-integrals.md)
- **Statement:** The actual character's logarithmic place Gaussian is absolutely integrable for `Re s > 0`, and twice its radial/unit-log integral equals `GammaFactor(s)/(degree*2^unitRank)`.

## Proof

Extend actual real-place character parities by zero at complex places.
Finite-product Fubini and the scalar logarithmic Gaussian integrals give
`GammaR(s+epsilon)/2` at each real place and `GammaC(s)/4` at each complex
place. Here `GammaC(s)=2*(2*pi)^(-s)*Gamma(s)`.

The proved radial/unit-log Jacobian is `2^r2/degree`; the substitution
`t=exp(2q)` contributes two. With `unitRank+1=r1+r2`, the remaining scalar is
exactly `1/(degree*2^unitRank)`. Absolute integrability follows from positive
real parts of every place exponent and the proved measure change.

Each real Gamma factor is nonzero on the positive half-plane.
`GammaR(s)*GammaR(s+1)=GammaC(s)` gives the same property at complex places.
The entire reciprocal of GammaR, finite products, affine composition, and
natural powers give the entire reciprocal of the actual Gamma product.

## Lean verification

Module: `HeckeLFunctions/HeckeGammaFactorsAreArchimedeanMellinIntegrals.lean`.

- `heckePlaceParity`, `sum_heckePlaceParity`, and
  `sum_heckePlaceParity_mul` identify the actual place parities.
- `heckeGammaFactor_ne_zero` and `differentiable_heckeGammaFactor_inv` give
  nonvanishing and the entire reciprocal.
- `integrable_heckeArchimedeanLogKernel` and its radial version prove
  absolute convergence.
- `integral_heckeArchimedeanLogKernel` evaluates independent-place integrals.
- `integral_heckeArchimedeanLogKernel_radial` proves the exact normalization.

Five main transitive axiom checks returned only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit passed without warnings:
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeGammaFactorsAreArchimedeanMellinIntegrals.lean`.
Wired into the Hecke umbrella; umbrella not compiled.

The actual element-kernel identification and class ideal-series exchange
remain on the active archimedean Mellin card.
