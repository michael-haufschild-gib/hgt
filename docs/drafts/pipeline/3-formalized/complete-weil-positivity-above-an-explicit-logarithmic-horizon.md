# Complete Weil positivity above an explicit logarithmic horizon

- **ID:** complete-weil-positivity-above-an-explicit-logarithmic-horizon
- **Stage:** 3-formalized
- **Statement:** For every `c≥1`, choose the proved conductor cutoff `R`
  for squared approximation error `1/4`, and set `Q=R+2`. Let `e(c)>0`
  be the actual common spectral-tail floor and let `B` exceed the sum of
  the proved residual constants for `1≤m≤Q`. The complete tilted-spline
  Weil matrix is positive definite whenever
  `N≥Q⁴`, `N≥Hc⁸`, `N≥4(e+3)²c²` (here `e=exp(1)`), and
  `log N≥max(1,36B(c⁵+c¹⁰)/e(c)²)`.
  The cutoff satisfies `Q≤exp(D(Cc¹⁶+1))+2`.

## Proof

A nonpositive unit eigenvector has a raw Ramanujan approximation of squared
error at most `1/4` through `R`. The harmonic frame at `N≥Q⁴`, followed by
Cauchy–Schwarz, gives squared coordinate mass at least `1/18` through `Q`.

For its eigenvalue `λ≤0` and a conductor mode of energy `E_m≥e(c)`, symmetry
gives `⟨(W−E_m)u_m,x⟩=(λ−E_m)⟨u_m,x⟩`. Thus its squared coordinate is
at most the squared residual divided by `e(c)²`.

Writing `L=log N>0`, the third positive exponential-series term gives
`(2L)³/6≤exp(2L)=N²`, hence `(L/N)²≤1/L`. The complete residual estimate
therefore bounds total coordinate mass by
`B(c⁵+c¹⁰)/(e(c)² log N)≤1/36`, contradicting `1/18`.
Every constant comes from an unconditional source estimate. No asymptotic
waiting horizon is used in this finite certificate.

## Verification

`CriticalArithmeticCorrelationTheory/CompleteConductorResidualsRetainTheirHorizonDecay.lean`:

- `exists_completeWeil_completedConductor_residual_explicit_horizon_bound`
- `exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_horizon`

Direct leaf check passed; both transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Existing umbrella import retained.
The range `0<c<1` and effective full-index schedule horizons remain separate obligations.
