# Littlewood Z3: the crude factorial estimate is lossy — use the exact interface

Correction to `route_e/littlewood_z3_per_block_explicit_2026_08_05`, same day.

## The error

`blockLambda_le_of_order` and `dirichlet_block_saving_of_range` derive the window-top hypothesis
from `(k−1)! ≤ (k−1)^{k−1} ≤ N^{k−1}` (needs `k−1 ≤ N`), giving `lam_k ≤ (t/2π)/(2^k N)` and hence
the hypothesis `t ≤ 2π·2^{k₀}·N^{2/3}`. That forces `2^{k₀} ≳ t/N^{2/3}`, i.e. **`k₀ ≈ log₂ t`**,
whereas the classical schedule needs **`k ≈ log t / log N`**. At `k₀ ≈ log₂ t` the saving
`N^{−1/(3·2^{k₀})}` is essentially 1 — the theorem is true but carries no saving.

Root cause: the estimate discards the entire gap between `(k−1)!` and `N^{k−1}`.

## The fix (built, unconditional)

`RHTower/Sieve/DirichletBlockSchedule.lean`:

- `blockLambda_le_iff (hN : 1 ≤ N) (k) (U)` :
  `blockLambda t N k ≤ U ↔ t·(k−1)! ≤ 2π·(2N)^k·U`. Exact; no factorial estimate baked in.
- `blockLambda_le_of_factorial_bound` — the `U = N^{−1/3}` case.
- `dirichlet_block_saving_of_factorial_range` — capstone with the exact window-top hypothesis:
  `8π N^{1/3} ≤ t`, `t·(k₀−1)! ≤ 2π(2N)^{k₀}N^{−1/3}`, `k₀ ≥ 2`, `N ≤ M ≤ 2N+1`
  ⟹ `‖∑_{Ico N M} n^{−1−It}‖ ≤ 2560·N^{−1/(3·2^{k₀})}`.

In log form the hypothesis is `k₀ log(2N) − log((k₀−1)!) ≥ log t + (1/3)log N`; with
`(k₀−1)! ≤ (k₀−1)^{k₀−1}` this is `k₀(log(2N) − log k₀) ≳ log t`, i.e. the classical
`k₀ ≈ log t/log N`. **This is the estimate the dyadic assembly must supply per block.**

## Lesson

When a lemma's hypothesis is derived through a convenience estimate, check the *scale* the
hypothesis then forces before building on it. Prefer the exact iff-form interface and let the caller
choose the estimate (same idiom as `distribution-blocker-is-over-scoped`: parameterize, don't guess).
