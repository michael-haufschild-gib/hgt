# The heat-count ladder at inverse-logarithmic heat

- **ID:** heat-ladder-inverse-log
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #10; frontier map WD
- **Statement:** With `N(t) = nonrealZeroCount t`: deep windows at depth `d` in `[X, 2X]` satisfy
  `#F ≤ C log X · N(c d²/log X)` uniformly in `0 < d ≤ ½`; hence `N(t) ≤ exp(A t^{−a})` gives
  `#F ≤ C log X exp(A (log X/(cd²))^a)`, `a < 1` gives `#F ≤ X^ε`, and `N(t) ≤ A t^{−a}` gives
  `#F ≤ C A log X (log X/(cd²))^a`.

## Lean
Module `RHTower/Heat/TheHeatCountLadderAtInverseLogarithmicHeat.lean` (namespace `RHTower.DeBruijn`):
`exists_deep_window_bound_at_inverse_log_heat`, `inverse_log_heat_le`,
`stretchedExponential_deep_density_of_nonrealZeroCount_at_inverse_log_heat`,
`subpower_deep_density_of_nonrealZeroCount_lt_one`,
`polylog_deep_density_of_polynomial_nonrealZeroCount_uniform`.
`eventually_log_mul_exp_rpow_le_rpow` in `TheHeatCountGrowthLadder` is now public and reused.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
Specialize `exists_card_deep_le_heat_count_at_uniform_depth_scale` to `t = c d²/log X`. Since
`d² ≤ 1`, `t ≤ t₀` once `log X ≥ c/t₀`, uniformly in `d`. Insert the growth law at that `t`:
`(c d²/log X)^{−a} = (log X/(c d²))^a`. For `a < 1` the stretched exponential
`C log X exp(K (log X)^a)` is eventually below `X^ε` (`eventually_log_mul_exp_rpow_le_rpow`).

## What it changes
`TheHeatCountGrowthLadder` transfers growth laws through the persistence time `δ²/(C log⁴ X)`, so
its exponent is `4a`, its subcritical range is `a < 1/4`, and its polylog exponent is `4a + 1`. The
corpus also proves persistence at `c d²/log X` (`HeatMeanFieldPersistence`,
`HeatUniformDepthZeroDensity`). Built on that time, the ladder has exponent `a`, range `a < 1` and
polylog exponent `a + 1`, uniformly in the depth. `a = 1` is the borderline: `exp(A/t)` at
`t ≍ 1/log X` is a power of `X`. So the WD receiver needs a heat-count bound `exp(A t^{−a})` with
some `a < 1`, not `a < 1/4`.

## Log
- 2026-10-31 — created; proved; formalized.
