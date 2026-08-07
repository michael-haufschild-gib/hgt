# Large values of the full series live in one window (2026-08-07)

`RHTower/Sieve/HalaszLargeValueWindow.lean` — green (9067 jobs), axiom-clean, in the umbrella.

- `sub_sq_mul_logSqWeight_le_of_norm_gt` : if `‖F(σ+it)‖` and `‖F(σ+iu)‖` both exceed
  `(1+1/(σ-1))·exp(7/2+shift-δ²)` and `|t-u|·log z ≤ π`, then `(t-u)²·logSqWeight z ≤ 2π²δ²`.
  Mechanism: contrapositive of `norm_tsum_twistedSummand_le_of_far` makes both frequencies close, then
  the corpus's `HalaszWindow.sq_sub_mul_logSqWeight_le` applies.
- `abs_sub_le_of_norm_gt` : hence `|t-u| ≤ √(2π²δ²/logSqWeight z)` — diameter `O(δ/log z)`.
- `abs_sub_mul_log_le_of_abs_sub_le` : on an interval of length `π/log z` the window lemma's smallness
  hypothesis is automatic (`log p ≤ log z` for `p ≤ z`).

**The `π/log z` restriction is real, not an artifact**: the window lemma needs `|(t-u) log p| ≤ π`
because the distance only sees the character mod its period. A bound over a LONG t-range must cover it
by intervals of that length — that covering is the next step, together with the Perron assembly
(`HTGeometry.SmoothWeightPerron`, stated for arbitrary coefficient sequences with `‖a n‖ ≤ 1`).

Lean note: `Real.le_sqrt` takes TWO nonnegativity arguments on this toolchain
(`Real.le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ √y ↔ x^2 ≤ y`).

See `mem:route_e/halasz_full_series_sum_2026_08_07`.
