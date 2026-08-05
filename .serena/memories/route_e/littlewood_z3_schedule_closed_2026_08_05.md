# Littlewood Z3: the order schedule is closed (2026-08-05)

Follows `route_e/littlewood_z3_block_saving_windows_2026_08_05`.

## New modules (built, wired, axioms `[propext, Classical.choice, Quot.sound]`)

`formal/GaloisForLFunctions/HTGeometry/RatioBoundedWindowLanding.lean`
- `exists_mem_window_of_ratio_lower_bound` — reusable. If `0 ≤ c`, `c * u (m-1) ≤ u m` for
  `m > start`, `L ≤ u start`, `L ≤ c * U`, and `∃ k ≥ start, u k ≤ U`, then
  `∃ k ≥ start, u k ∈ [L, U]`.
  Proof: `Nat.find` the least index dropping below `U`; the previous value exceeds `U`, so the ratio
  bound keeps this one above `c*U ≥ L`. **No optimisation, no balancing** — this is the whole
  content of an "order schedule".

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSchedule.lean` (namespace `RHTower.Sieve`)
- `blockLambda t N k = (t/2π)(k−1)!/(2N)^k` — matches the expression in
  `dirichlet_block_one_normalized` verbatim so it rewrites without massaging.
- `blockLambda_ratio` : for `m ≥ 3`, `lam_m ≥ lam_{m−1}/N` (exact ratio `(m−1)/(2N)`).
- `exists_blockLambda_in_window` : width condition is `N^{−5/3} ≤ (1/N)·N^{−1/3} = N^{−4/3}`, true
  for **every** `N ≥ 1`. (The `N ≥ 8` from the informal width-vs-step picture is not needed.)
  Hypotheses reduce to `lam_2 ≥ N^{−5/3}` and `∃ k ≥ 2, lam_k ≤ N^{−1/3}`.
- `exists_dirichlet_block_saving` : capstone —
  `∃ k ≥ 2, ‖∑_{Ico N M} n^{−1−It}‖ ≤ 2560·N^{−1/(3·2^k)}` for `N ≤ M ≤ 2N+1`.

## Remaining in Z3

Head/tail split against `Sieve/HarmonicLogBound`; discharge the two schedule hypotheses on tail
blocks from a `t`-versus-`N` branch; sum `2560·N^{−1/(3·2^k)}` over dyadic `N`. Then Z4
(PNTPlus truncation) and Z5 (rectangle `σ`-version via `abel_block_bound` with `w n = n^{−σ}`).

## Lean notes

- `div_le_div_iff` is gone → `div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d)`.
- `i + 2 - 1` does not reduce under `Nat.add_sub_cancel` (that matches `n + m - m`); supply
  `have : i + 2 - 1 = i + 1 := by omega` and rewrite.
- `field_simp` frequently closes the goal outright; a trailing `ring` then errors "No goals".
- Narrow imports for a plain ℝ lemma: `Mathlib.Algebra.Order.Ring.Defs` does **not** bring the ℝ
  instances; use `Mathlib.Data.Real.Basic`.
