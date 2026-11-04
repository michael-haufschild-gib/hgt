# Polynomial profile for the fifth even cross-load

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** Replace the fixed cross-load by the derivative of a polynomially
  weighted center flux, preserving the integrated moments and restoring
  positivity through the compact source interval.

Let `P(r)=(1-r²/2)²`. Its flux is
`polynomialFlux 0 − polynomialFlux 2 + polynomialFlux 4/4`.
The proposed aperture-independent correction is

`G_P(x)=(1−2x²)²G(x)−8x²(1−2x²)F(x)²`.

At `x₈=½log(8/π)`, the existing source bounds imply `G≤−6F²`.
The center bounds give `(1−2x²)²≤1/3`, while
`8x²(1−2x²)≤1` follows from `(1−4x²)²≥0`.
Hence `G_P≥G/3−F²≥G/2`; the positive half-load would repair this point.

The local comparison and the zero-integral identity require Lean formalization.
The expansion `G_P=(3−20x²+28x⁴)F²+(2x−8x³+8x⁵)FF′` gives
`G_P/(f₁²q⁴)→0` from the existing first-atom mass and slope limits and
exponential domination of powers. The cross-load vanishes in entries with
`i+j<4`, so Gaussian balancing predicts a strictly positive cofinal ray.

Positivity throughout the intervening compact interval remains open.
Polynomial growth alone does not control that interval's tail debt.
