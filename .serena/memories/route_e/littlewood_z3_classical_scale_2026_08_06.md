# Littlewood Z3: window-top condition at the classical scale (2026-08-06)

Completes `route_e/littlewood_z3_factorial_estimate_correction_2026_08_05`.

`RHTower/Sieve/DirichletBlockSchedule.lean`, built, axioms `[propext, Classical.choice, Quot.sound]`.

- `blockLambda_le_of_small_factorial` : `k ≥ 1`, `(k−1)! ≤ N` (naturals),
  `t ≤ 2π·2^k·N^{k−1}·N^{−1/3}` ⟹ `lam_k ≤ N^{−1/3}`.
  Mechanism: `t·(k−1)! ≤ t·N ≤ 2π·2^k·N^{k−1}·N^{−1/3}·N = 2π·(2N)^k·N^{−1/3}`.
- `dirichlet_block_saving_of_small_factorial` : capstone at that scale.

Hypothesis reads `t ≈ N^{k−4/3}`, i.e. **`k ≈ log t/log N + 4/3` — the classical schedule, no loss.**

Why `(k−1)! ≤ N` is comfortable: the assembly uses `N ≥ t^{1/m}`, `m ≈ loglog t`, so `k ≤ m` and
`(k−1)! ≤ (loglog t)^{loglog t} = (log t)^{o(1)}` while `N ≥ exp(log t/m)`. The factorial itself was
never the problem — only the crude bound `(k−1)! ≤ N^{k−1}`, which is of size `t`.

## Three tiers of the same conclusion (pick the right one)

1. `dirichlet_block_saving_of_range` — crude (`k−1 ≤ N`, `t ≤ 2π·2^{k₀}N^{2/3}`); forces
   `k₀ ≈ log₂ t`; **no saving; do not use**.
2. `dirichlet_block_saving_of_factorial_range` — exact hypothesis `t·(k₀−1)! ≤ 2π(2N)^{k₀}N^{−1/3}`;
   caller supplies any factorial estimate.
3. `dirichlet_block_saving_of_small_factorial` — classical scale via `(k₀−1)! ≤ N`. **Use this.**

## Next

Head/tail split against `Sieve/HarmonicLogBound`; sum `2560·N^{−1/(3·2^{k₀})}` over dyadic `N` with
per-block `k₀ ≈ log t/log N`; then Z4 (PNTPlus truncation), Z5 (rectangle σ-version).

## Lean note

`rw [mul_pow]` then `congr 1` mis-splits `2^k * N^k = 2^k * N^{k−1} * N`. Prove
`N^k = N^{k−1} * N` separately (via `obtain ⟨j, rfl⟩ : ∃ j, k = j+1` and `simp [pow_succ]`) and
finish with `rw [mul_pow, hNk, ← mul_assoc]`.
