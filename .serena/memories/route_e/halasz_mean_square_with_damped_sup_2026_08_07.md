# The mean-square estimate with the damped sup (2026-08-07)

`RHTower/Sieve/HalaszMeanSquare.lean` — green (9081 jobs), axiom-clean, umbrella-wired. Third and last
brick of the successor task of `mem:route_e/halasz_route_loses_log_squared_2026_08_07`.

- `integral_norm_dirPoly_le_of_sup_on` / `integral_norm_dirPoly_halasz_on` — the corpus's
  `integral_norm_dirPoly_le_of_sup` / `_halasz` with the sup hypothesis weakened from `∀ t` to
  `∀ t ∈ Ioc 0 T`. The original proof only evaluates the sup inside the integral, so this is a strict
  generalisation; `0 ≤ M` is also unnecessary in the first form (the empty-range case is `0 ≤ 0`).
- `integral_norm_dirPoly_twisted_halasz` :
  `∫_{Ioc 0 T} ‖dirPoly L (twistedTruncCoeff f σ L) u‖ ≤ V·T +
    (damped + L^(1-σ)/(σ-1))·((T + 4L(1+log L))·∑ ‖a m‖²)/V²`
  with `damped` from `HalaszUniformDistance.norm_tsum_twistedSummand_le_damped_of_uniform` and the
  truncation error from `DirichletTruncationError`.

**Why this is the point:** the sup multiplying the level-set measure is now the DAMPED size, not the
trivial `∑|aₙ| ≍ log L`, and `∑|aₙ|² = O(1)` uniformly in `L`
(`sum_norm_sq_twistedTruncCoeff_le`). This is the ingredient whose absence made the pointwise route
`(log N)²` short.

## Still open

The optimisation over `V` and the parameter choice (`σ, z, δ, L, T`). Until that is done there is NO
decay claim — the same discipline as before.

## Lean note

Use `norm_sub_le a (a - b)` + `rw [sub_sub_cancel]` for `‖b‖ ≤ ‖a‖ + ‖a - b‖`; writing the `ring`
rearrangement by hand leaves the norm's type as a metavariable and typeclass search gets stuck.
