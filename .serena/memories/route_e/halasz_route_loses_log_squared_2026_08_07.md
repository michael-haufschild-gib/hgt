# CORRECTION: the Halász chain loses (log N)², and the earlier repair list was wrong (2026-08-07)

Supersedes `mem:route_e/halasz_parameter_audit_no_decay_yet_2026_08_07` (its two "repairs" address the
wrong step) and puts `mem:route_e/character_distance_window_free_2026_08_07` off the critical path
(still a correct, reusable result).

## The exceptional set is a non-issue

`MoebiusUniformFrequency.exists_mulDistSqPair_ge_uniform` is a lower bound UNIFORM over `|t| ≤ T` —
i.e. it IS Halász's `M = min_{|t| ≤ T} D(f,n^{it};z)²`. Taking `δ² = M` makes the hypothesis of
`norm_tsum_twistedSummand_le_of_far` true at EVERY `t`, so the damped bound is pointwise on the whole
range. No window, no covering, no large-value set. `HalaszLargeValueWindow` and
`DiameterCoveringMeasure` are correct but not needed for this route.

## The real loss: a factor (log N)²

`2π‖∑ f(n)w(n)‖ ≤ damped · ∫_ℝ‖W‖` with `damped ≍ log N · e^{-M}` and `∫_ℝ‖W‖ ≍ N²/H` (two
integrations by parts: `‖W(σ+iy)‖ ≲ (N+H)^{σ+1}/(H‖s(s+1)‖)`); with `H = N/log N` that is `N log N`.
So `‖∑‖ ≲ N (log N)² e^{-M}`, and `o(N)` needs `M > 2 log log N`. For μ the truth is `M ≈ log log N`,
which Halász's `(1+M)e^{-M}` consumes exactly — his prefactor is `1+M ≍ log log N`, not `(log N)²`.

## Why it is structural, not a constant

`∫‖F‖‖W‖ ≤ (sup‖F‖)·∫‖W‖` discards all cancellation of `F` across the range. Halász bounds `∫‖F‖` by a
MEAN-VALUE estimate: corpus `DirichletMeasureLargeValues.integral_norm_dirPoly_halasz`
(`∫₀^T‖F‖ ≤ V·T + M·|{‖F‖ ≥ V}|`) plus `DirichletIntegralMeanValue` (`|∫₀^T|F|² − T∑|aₙ|²| ≤
4N(1+log N)∑|aₙ|²`). Those use `∑|aₙ|²`, never `sup‖F‖`.

## Discipline

Every module of the chain is still needed by the mean-square route (Euler bound, trivial size, distance
bridge, Perron assembly). But do NOT attempt a decay statement through the pointwise route: it cannot
reach `o(N)` for μ. The next real step is the mean-square input, applied to the truncated Dirichlet
polynomial rather than to the full series.
