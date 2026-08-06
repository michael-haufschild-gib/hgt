# Littlewood Z3: choosing the split point (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSplitPointChoice.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

Upper `t`-bound is `t ≤ 2π·2^{σ(K−4/3)+K}` with `σ = S+1`, so the least admissible `σ` is
`⌈x⌉₊` for the balance point
`x = (log(t/2π) − K·log 2) / ((K − 4/3)·log 2)`.

- `splitExponent t K := ⌈x⌉₊`
- `le_two_pow_splitExponent` : that choice satisfies the upper `t`-bound.
- `splitExponent_arg_nonneg (hK : 2 ≤ K) (hbig : 2π·2^K ≤ t)` : `0 ≤ x`.
- `splitExponent_le (hx : 0 ≤ x)` : `σ ≤ x + 1`.

Both directions are what the estimate needs: upper bound holds, and the harmonic head `σ·log 2`
exceeds `x·log 2 = (log(t/2π) − K log 2)/(K − 4/3)` by less than `log 2`. For `K ≈ m` the head is
`log t/m` up to bounded terms — the source of the `loglog` saving.

## Lean notes

- `Nat.ceil_lt_add_one` **requires** `0 ≤ a` (there is also `Nat.ceil_lt_add_one_of_gt_neg_one`
  for `−1 < a`). `exact?` does not find either from a bare `⌈x⌉₊ ≤ x + 1` goal.
- `Real.log_pow : Real.log (x ^ (n : ℕ)) = n * Real.log x`.
