# Littlewood Z4 CLOSED: a bound on ζ(1+It) itself (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/ZetaLineLittleOh.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

```
lineTruncation t := 2^{topExponent t + 1} − 1

norm_riemannZeta_line_littleOh (hε : 0 < ε) :
  ∃ T, ∀ t ≥ T,
    ‖ζ(1 + It)‖ ≤ 1 + log 2 + ε·log(t/2π) + 1/t + (1+t)/((t/(8π))³ − 1)
```

Head = derivative-test bound transported through the truncation; both tail terms explicit and → 0
(the second because the chain's truncation point grows like the **cube** of `t` while `‖1+It‖` is
linear — a huge margin, not delicate).

**This is a bound on ζ itself, not a partial sum, and it is unconditional.**
Z3 + Z4 now run from the k-th derivative test to the qualitative `ζ(1+it) = o(log t)`.

## Remaining on the card

- quantitative exponent: `K` growing with `t` ⟹ `O(log t/loglog t)`
- Z5: rectangle σ-version (reuse `abel_block_bound` with `w n = n^{−σ}`)
- then `PNTPlus/ZetaBounds`'s Landau/3-4-1 pipeline consumes the rectangle version → zero-free region

## Lean notes

- `pow_le_pow_left` → `pow_le_pow_left₀`; `div_le_div` (4-arg) is gone — compose
  `div_le_div_of_nonneg_right` (numerator, `0 ≤ denom`) with
  `div_le_div_of_nonneg_left (0 ≤ a) (0 < b) (b ≤ c) : a/c ≤ a/b`.
- `omega` cannot see through `2 ^ (e + 1)`; `rw [defn]` first and supply
  `2 ≤ 2^(e+1)` as a hypothesis.
- `push_cast at this ⊢` can normalise `((2^k : ℕ) : ℝ)` to a real power on one side only — state the
  cast identity as its own `have` in the exact shape needed, then `linarith`.
