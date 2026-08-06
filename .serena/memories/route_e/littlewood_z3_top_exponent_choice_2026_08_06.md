# Littlewood Z3: choosing the top of the range (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTopExponentChoice.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

Lower `t`-bound is `8π·2^{R/3} ≤ t`, so the largest admissible `R` is `⌊3 log(t/8π)/log 2⌋₊`.

- `topExponent t := ⌊3·log(t/(8π))/log 2⌋₊`
- `topExponent_arg_nonneg`, `topExponent_le (ht : 8π ≤ t)` : `R ≤ 3 log(t/8π)/log 2`
- `topExponent_bound (ht : 8π ≤ t)` : `8π·2^{R/3} ≤ t`

## Both exponents are now explicit functions of `t` and `K`

```
σ = S+1 = ⌈(log(t/2π) − K·log 2) / ((K − 4/3)·log 2)⌉₊        (DirichletSplitPointChoice)
R       = ⌊3·log(t/(8π)) / log 2⌋₊                            (this module)
```

and the exponent-form conclusion becomes
`1 + σ log 2 + (R−S)ε ≤ 1 + [(log(t/2π) − K log2)/(K−4/3) + log 2] + [3 log(t/8π)/log 2]·ε`.

With `K ≈ m`, `ε ≈ 1/m` both brackets are `O(log t/m)`; the depth criterion forces
`m ≈ log₂log₂ t`. **Only `ε` and `K` remain to be tied to `t`.**

## Lean note

`R ≤ 3L/log 2 ⟹ (R/3)·log 2 ≤ L`: do NOT try `div_le_div_iff₀` on the goal. Use
`mul_le_mul_of_nonneg_right hle hlog2.le`, then `div_mul_cancel₀ _ hlog2.ne'`, then `linarith`.
