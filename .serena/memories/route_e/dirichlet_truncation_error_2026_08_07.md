# The truncation error, entry point to the mean-square route (2026-08-07)

`RHTower/Sieve/DirichletTruncationError.lean` — green (9023 jobs), axiom-clean, umbrella-wired.

- `tsum_tail_rpow_neg_le (hσ : 1 < σ) (hL : 1 ≤ L) : ∑' j, ((j+L+1 : ℕ):ℝ)^(-σ) ≤ L^(1-σ)/(σ-1)` —
  integral test from `L` (`AntitoneOn.tsum_comp_add_le_integral L` + `integral_Ioi_rpow_of_lt`), reusing
  my `antitoneOn_rpow_neg_Ici`.
- `norm_tsum_sub_sum_range_le` / `_le_pow` : `‖∑' n, f n·n^(-s) − ∑_{n ≤ L} f n·n^(-s)‖ ≤ L^(1-σ)/(σ-1)`.

**Why it was missing:** every corpus mean-square estimate (`DirichletIntegralMeanValue`,
`DirichletMeasureLargeValues`) is about a Dirichlet POLYNOMIAL of finite length; the Euler bound is about
the whole series. This is the passage. At `σ = 1 + A/log L` the error is `e^{-A}(log L)/A`.

## Lean notes

- `Summable.sum_add_tsum_nat_add k` exists only as the `to_additive` image of
  `Multipliable.prod_mul_tprod_nat_add`, so it is not greppable as a `theorem`. Finish the split with
  `rw [← hsplit, add_sub_cancel_left]` — `ring` on that term blows the heartbeat budget.
- `set_option maxHeartbeats 1000000 in` was needed for the truncation lemma even so.
- `neg_div_neg_eq` turns mathlib's `-c^(a+1)/(a+1)` into the `L^(1-σ)/(σ-1)` shape after rewriting both
  `-σ+1` and `1-σ` as `-(σ-1)`.

Next on the route: feed the truncated polynomial to `integral_norm_dirPoly_halasz` /
`volume_largeValues_le` and compare with the damped sup bound.
