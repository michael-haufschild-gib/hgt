# Littlewood Z3: canonical target — only the order K remains free (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTargetEps.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

Depth criterion `3·2^K·log(2560/ε) ≤ σ·log 2` is a **lower** bound on `ε`, so the best target makes
it an equality:

`targetEps σ K := 2560 · exp(−σ·log 2 / (3·2^K))`

- `targetEps_pos`, `targetEps_le` : `0 < targetEps ≤ 2560`
- `targetEps_deep` : `3·2^K·log(2560/targetEps) = σ·log 2` (**equality** — nothing wasted)
- `norm_dirichlet_partial_littlewood_canonical` :
  `‖∑_{n<2^{R+1}} n^{−1−It}‖ ≤ 1 + [(log(t/2π) − K log2)/((K−4/3) log2) + 1]·log 2
     + [3 log(t/8π)/log 2]·targetEps (splitExponent t K) K`

Every parameter except `K` is a function of `t`. Remaining hypotheses: `1 ≤ σ`, `σ−1 < R`,
`(K−1)! ≤ 2^σ`, plus `8π ≤ t` and `2π·2^K ≤ t`.

## The cap on K, now visible in the formula

Tail term is `3 log(t/8π)/log2 · 2560 · exp(−σ log2/(3·2^K))` with `σ ≈ log t/(K log 2)`, so the
exponent is `≈ −log t/(3K·2^K)`. Tail is `O(log t/K)` iff `exp(−log t/(3K·2^K)) = O(1/K)` iff
`2^K·K·log K ≲ log t/3` — the same cap `K ≈ log₂ log t` the regime analysis gave, now readable
directly off the closed formula rather than derived separately.

## Remaining for Z3

Choose `K` as a function of `t` (e.g. `K = ⌊log₂ log t⌋ − c`), discharge `(K−1)! ≤ 2^σ`,
`1 ≤ σ`, `σ−1 < R`, and conclude `O(log t/loglog t)`.
