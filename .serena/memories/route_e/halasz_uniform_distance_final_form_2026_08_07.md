# The pointwise route, in its correct final form (2026-08-07)

`RHTower/Sieve/HalaszUniformDistance.lean` — green (9075 jobs), axiom-clean, umbrella-wired.

Acting on `mem:route_e/halasz_route_loses_log_squared_2026_08_07`: a UNIFORM distance lower bound on
`|t| ≤ T` (= Halász's `M = min_{|t|≤T} D²`) makes the damped bound hold at every frequency, so the
window/covering layer drops off the critical path.

- `norm_tsum_twistedSummand_le_damped_of_uniform` : `∀ t, |t| ≤ T → δ ≤ √(mulDistSqPair f (charFn t)
  (primesLE z))` ⇒ the damped bound at each such `t`.
- `norm_tsum_mul_smoothWeight_le_of_uniform` :
  `∃ C ≥ 0, 2π‖∑' n, f n · w(n)‖ ≤ ((N+H)^σ/σ)·damped·2T + trivial·C·(π − 2 arctan T)`.
  Strictly sharper than `HalaszPerronAssembly.norm_tsum_mul_smoothWeight_le` — the `T·δ` window term is
  gone.

This is the ENDPOINT of the pointwise route: size `N(log N)²e^{-M}`, i.e. `(log N)²` short of Halász.
No sharpening of the pointwise argument removes it; the mean-square input is a different theorem.

Reusable independent of the route: `DiameterCoveringMeasure` (general), `CharacterDistanceLower`
(window-free character distance), `PrimeCosineSumUpper` (the mirror passage), `MultiplicativeEulerBound`,
`PrimeAbscissaSumBound`, `DistanceAbscissaBridge`.
