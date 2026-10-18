# APT stage-2 → stage-3 formalization status

## Done (moved to `3-formalized/`)
- `APT-ROOT-RAMP-LIMIT` — [card](../../3-formalized/arithmetic-positivity-factorial-ramp-smoothing-limit.md); Lean: `FactorialRampFullWeilSmoothingLimit.lean` (`factorialMuntzSmoothedRamp_weilFullFunctional_tendsto_span`, `re_weilFullFunctional_smooth_tendsto`).
- `APT-ROOT-RAMP-MARGIN` — [card](../../3-formalized/arithmetic-positivity-factorial-ramp-gram-margin.md); Lean: `factorialSpanWeil_rampTent_margin`, `factorialSpanWeil_ramp_log_bounds`, `factorialMuntzSmoothedRamp_re_W_tendsto`.

## Remaining in `2-fully-proven/apt`
The earlier modules for these three cards prove only scalar arithmetic (constants, collar spacing,
filter coefficients). The literal analytic statements are still open in Lean:

- `APT-ROOT-WINDOW` (window coercivity): Bernoulli cosine expansion of `Φ_N`
  (from `RHTower.hasCosDivSq`-type `hasSum_cos_div_sq`), harmonic layers `H_k` as Montgomery–Vaughan
  exponential sums (`interval_integral_normSq_expSum_ge/le`, gap `k/15`), first-harmonic dominance
  `|x+y|² ≥ (1-θ)|x|² + (1-1/θ)|y|²` with θ = 4/5, weighted transport to `∫_1^∞ v^{-4}`, and the
  change of variables `v = e^{-x}` giving (3).
- `APT-ROOT-BOHR` (Bohr coercivity): Bohr square mean existence via Tannery over the double harmonic
  series, vanishing mixed mean (irrationality), periodic mean of the integer family, `L²(0,1)`
  orthogonality, θ = 3/4 dominance, linear independence of the tails.
- `APT-ROOT-SPAN-COERCIVITY`: needs WINDOW, dilated window bounds (4), literal Mellin
  nonstationary bound, Plancherel, Gamma quarter inequality, prime/polar budgets, and the
  four-channel smoothing passage for the complex tail combinations.
