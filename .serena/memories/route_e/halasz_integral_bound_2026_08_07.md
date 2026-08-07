# Halász's mean-value estimate for the full series (2026-08-07)

`RHTower/Sieve/HalaszIntegralBound.lean` — green (9069 jobs), axiom-clean, in the umbrella.

- `continuous_tsum_twistedSummand` : `Continuous fun t => ∑' n, f n · n^(-(σ+it))` for `|f| ≤ 1`,
  `σ > 1`, via mathlib's `continuous_tsum` (Weierstrass) against `∑ n^{-σ}`. Consequence: the
  large-value set is OPEN, hence measurable — that is what makes the integral split legal.
- `integral_norm_tsum_twistedSummand_le` :
  `∫_{Icc (-T) T} ‖F(σ+it)‖ ≤ damped·2T + trivial·(2T log z/π + 1)·2√(2π²δ²/logSqWeight z)`,
  `damped = (1+1/(σ-1))e^{7/2+shift-δ²}`, `trivial = (1+1/(σ-1))e^{7/2}`.
  Proof: `integral_inter_add_sdiff` at the damped level; `setIntegral_mono_on` + `setIntegral_const`
  on each piece; the window measure from `volume_largeValues_le`.

## The thread is complete except Perron

local factor → full series → trivial size → harmonic-distance bridge → dichotomy/discrete large values
→ window confinement → covering measure → t-integral. Only the Perron assembly remains, and
`HTGeometry.SmoothWeightPerron.tsum_mul_smoothWeight_eq_integral` is already stated for an ARBITRARY
coefficient sequence with `‖a n‖ ≤ 1`.

## Lean names that moved on this toolchain

- `setIntegral_inter_add_diff` → **`integral_inter_add_sdiff`** (`Bochner/Set.lean`).
- `integrableOn_const_of_ne_top` → **`integrableOn_const (hs : μ s ≠ ∞)`**.
- `Set.diff_subset` deprecated → `sdiff_subset`. `le_of_not_lt` → `not_lt.mp`.
- `setIntegral_const` now returns `μ.real s • c`; unfold with `measureReal_def` + `smul_eq_mul`.
- `Continuous.const_cpow (hf) (Or.inl hne)` for `t ↦ b ^ (g t)` with `b ≠ 0`.

See `mem:route_e/halasz_covering_measure_2026_08_07`.
