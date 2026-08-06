# Littlewood Z3: factorial hypothesis discharged — all three now follow from t (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletFactorialHypothesis.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`factorial_le_two_pow_splitExponent (hK : 2 ≤ K)` :
`(K−1)(K−4/3)·log(K−1) + K·log 2 ≤ log(t/2π)` ⟹ `(K−1)! ≤ 2^σ`.

Mechanism: `σ ≥ x` (ceiling), `(K−1)! ≤ (K−1)^{K−1} = exp((K−1)log(K−1))`, and the hypothesis says
exactly `(K−1)log(K−1) ≤ x·log 2`.

## All three structural hypotheses are now consequences of largeness in t

| hypothesis | sufficient condition |
|---|---|
| `1 ≤ σ` | `2π·2^K < t` |
| `σ−1 < R` | `16π ≤ t` (plus `2π·2^K ≤ t`) |
| `(K−1)! ≤ 2^σ` | `(K−1)(K−4/3)log(K−1) + K log2 ≤ log(t/2π)` |

**The third dominates the first** (it implies `K log2 ≤ log(t/2π)`, i.e. `2π·2^K ≤ t`), so the whole
set reduces to `16π ≤ t` plus the single inequality
`(K−1)(K−4/3)log(K−1) + K log2 < log(t/2π)`.

In the regime `K ≈ log₂log t` the left side is `≈ (loglog t)²·logloglog t ≪ log t`.

## Remaining for Z3

Pick `K` as a function of `t` satisfying that inequality **and** the depth cap
`2^K·K·log K ≲ log t/3`, then read off `O(log t/loglog t)`.

## Lean note

`(L − K log2)/((K−4/3)·log2) · log2 = (L − K log2)/(K−4/3)`: don't chain
`div_mul_eq_mul_div / div_self / mul_one` rewrites — state it as a `have … := by field_simp` with
`Real.log 2 ≠ 0` and `(K:ℝ)−4/3 ≠ 0` already in context, then `rw` it.
