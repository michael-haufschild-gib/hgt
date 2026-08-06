# Littlewood Z3: two of three structural hypotheses discharged (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletStructuralHypotheses.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `one_le_splitExponent (hK : 2 ≤ K) (hbig : 2π·2^K < t)` : `1 ≤ σ`.
- `splitExponent_sub_one_lt_topExponent (hK) (ht16 : 16π ≤ t) (hbig : 2π·2^K ≤ t) (hσ1)` :
  `σ − 1 < R`.

## The comparison, and why 16π

The balance point `x = (L − K log2)/((K−4/3) log2)`, `L = log(t/2π)`, is **decreasing in K**
(numerator falls, denominator rises), so it is largest at `K = 2`: `x ≤ 3(L − 2log2)/(2 log 2)`.
`R > 3 log(t/8π)/log2 − 1` and `log(t/8π) = L − 2log2`, so the comparison reduces to

`(3/2)(L − 2log2) + log2 ≤ 3(L − 2log2)` ⟺ `L ≥ (8/3) log 2` ⟺ `t ≥ 2π·2^{8/3}`,

and `16π` suffices since `2^{8/3} < 8`. **No numeric estimate of π anywhere.**

## Remaining

Only the factorial bound `(K−1)! ≤ 2^σ`. With `σ ≈ log t/(K log2)` and `K ≈ log₂log t` this reads
`(log₂log t)! ≤ t^{1/K}` — comfortable, not yet formal.

## Lean notes

- `Nat.one_le_ceil_iff : 1 ≤ ⌈a⌉₊ ↔ 0 < a`.
- `Nat.lt_floor_add_one (a) : a < ⌊a⌋₊ + 1` (no nonnegativity needed).
- For `a/b ≤ c/d` with `a ≤ c`, `0 < d ≤ b`: `exact?` finds nothing; use
  `rw [div_le_div_iff₀ hb hd]` then `nlinarith` with the factored product as an explicit hint
  (here `(K−2)(L − 4log2/3)·log2 ≥ 0`, which is exactly RHS − LHS).
