# A two-sided digamma bound on the positive reals

- **ID:** DIG-2S-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** built while sharpening the pole bound for MUST-271
- **Statement:** `log y − 1/y ≤ Re ψ(y) ≤ log y` for every `y > 0`.

## What is proved

- `RHTower.re_digamma_le_log` (in
  [`DigammaLeLog`](../../../../formal/GaloisForLFunctions/RHTower/DigammaLeLog.lean)) — the upper
  bound. The `n`-fold recurrence `Re ψ(y) = Re ψ(y+n) − Σ_{k<n} 1/(y+k)`, the corpus's
  `‖ψ(z) − log z‖ ≤ 3/‖z‖` at `y+n`, and `Σ_{k<n} 1/(y+k) ≥ log(y+n) − log y` give
  `Re ψ(y) ≤ log y + 3/(y+n)` for every `n`; let `n → ∞`.
- [`DigammaTwoSided`](../../../../formal/GaloisForLFunctions/RHTower/DigammaTwoSided.lean):
  - `RHTower.inv_succ_le_log_one_add_inv` — `1/(m+1) ≤ log(1 + 1/m)` for `m > 0`.
  - `RHTower.harmonic_le_log_add_inv` — `Σ_{k<n} 1/(y+k) ≤ 1/y + log(y+n−1) − log y` for `n ≥ 1`.
  - `RHTower.log_sub_inv_le_re_digamma` — **`log y − 1/y ≤ Re ψ(y)`**, by the same shift-and-limit.

## Why it is worth having

Mathlib's `Complex.digamma` API carries only `digamma_one`, `digamma_one_half`,
`digamma_apply_add_one` and meromorphy — no size bound at all. The corpus's
`HTGeometry.norm_digamma_sub_log_le_of_re_pos` gives `‖ψ(z) − log z‖ ≤ 3/‖z‖` but needs `‖z‖ ≥ 2`.
On the positive reals the bound above is both sharper (`1/y` against `3/y`) and unrestricted, and it
is sharp in order: the true asymptotic is `log y − 1/(2y)`.

Its first use was the pole bound `−ζ'/ζ(σ) ≤ 1/(σ−1) − 1/5`, which is what widened the zero-free
region from `1/100` to `1/58` while keeping validity from ordinate `4`.

## Log
- 2026-09-24 — created; both bounds proved in Lean.
