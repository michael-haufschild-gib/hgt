# Littlewood Z3: power-of-two split removes all composite logs (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletPowerTwoShape.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_partial_littlewood_pow_two` — `norm_dirichlet_partial_littlewood_const` at `A = 2`:

```
2 ≤ K,  S < R,  0 < ε ≤ 2560,
(K−1)! ≤ 2^{S+1},
t ≤ 2π·2^K·(2^{S+1})^{K−1}·(2^{S+1})^{−1/3},
3·2^K·log(2560/ε) ≤ (S+1)·log 2,
8π·(2^R)^{1/3} ≤ t
  ⟹ ‖∑_{n < 2^{R+1}} n^{−1−It}‖ ≤ 1 + (S+1)·log 2 + (R−S)·ε
```

Every block base is a power of two, so both logarithms are multiples of `log 2`. **No `Real.log` of
a composite natural survives** in hypotheses or conclusion — the rest is arithmetic in `S, R, K, ε`.

## Regime

`R ≈ 3 log₂ t` (top condition), `S+1 ≈ (log₂ t)/m`, `K ≈ m + 2`, `ε ≈ 1/m`, with `m ≈ log₂log₂ t`
forced by `3·2^K·log(2560m) ≤ (S+1)·log 2`. Conclusion
`1 + (log₂ t)(log 2)/m + 3(log₂ t)/m = O(log t/loglog t)`.

## Lean trap

`Finset.Ico 1 (2 ^ (R+1))` inside a statement whose summand is `(n : ℂ) ^ …` elaborates the range
endpoints at **ℂ**, then fails on `Preorder ℂ` / `LocallyFiniteOrder ℂ`. Annotate:
`Finset.Ico (1 : ℕ) (2 ^ (R+1))`.
`Real.log_le_log_of_le` does not exist on this toolchain; use `Real.log_le_log (hx : 0 < x) (h : x ≤ y)`.
