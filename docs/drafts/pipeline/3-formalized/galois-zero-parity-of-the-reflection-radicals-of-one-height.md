# The reflection radicals of one height carry the parity of its zeros

- **ID:** gtz-parity-of-the-reflection-radicals
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, problem 3 (source parity on the reflection radicands; review-1411 §2.19).
- **Statement:** `U_t` the zeros with `Im ρ = t`, `A_{t,p} = ∏_{ρ∈U_t} (p^ρ − p^{1−ρ})`.
  (A) `c(A_{t,p}) = (−1)^{|U_t|} A_{t,p}`;
  (B) `σ(A_{t,p}) = ±A_{t,p}` for every `σ ∈ G`; `A_{t,p}² = ∏_{ρ∈U_t}(p^ρ − p^{1−ρ})² ∈ B`;
  (C) `|U_t|` is odd iff `½ + it` is a zero;
  (D) for each zero at most one prime kills its radical; some prime has `A_{t,p} ≠ 0`;
  (E) if `½ + it` is a zero, some prime makes `A_{t,p}²` a negative element of `B` that is not a
  square in `B`;
  (F) a lift `σ` of the reflection has `σ(A_{t,p}) = c(A_{t,p})`;
  (G) if `∏_{t∈T} A_{t,p_t}² = b²` with `b ∈ B` and all `A_{t,p_t} ≠ 0`, then an even number of
  the heights in `T` carry a critical zero.

## Goal

A source-derived parity on the reflection radicands: the class of the product of the radicands
of one height in `B^×/B^{×2}` is read off from the zeros of that height. Outcome: the class is
nontrivial and negative exactly at heights carrying a critical zero; a lift of `r` acts on it as
`c`, so the class is compatible with a lift and does not force `r = c`.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

(A) `c(p^ρ − p^{1−ρ}) = p^{ρ̄} − p^{1−ρ̄} = −(p^{1−ρ̄} − p^{ρ̄})`, and `ρ ↦ 1 − ρ̄` permutes `U_t`.
(B) `σ` permutes the zeros of `|Im| = |t|` commuting with `r`; `f(ρ) = σρ` or `1 − σρ`
(whichever has `Im = t`) is injective on `U_t` (`σρ₁ = 1 − σρ₂` would give `t = −t`), hence a
bijection, and the squares `(p^z − p^{1−z})²` are `r`-invariant: `σ(A)² = A²`. Fixed by `G`,
so in `B`. (C) `ρ ↦ 1 − ρ̄` pairs `Re < ½` with `Re > ½`; the critical zeros of `U_t` are at most
`½ + it`. (D) `p^ρ = p^{1−ρ}` and `q^ρ = q^{1−ρ}` give `ρ = 1 − ρ` (two primes), impossible;
finitely many zeros, infinitely many primes. (E) `c(A) = −A` makes `A` purely imaginary, `A² < 0`;
`A² = b²` with `b ∈ B` gives `A = ±b ∈ B`, then `A = −A`, `A = 0`. (F) `σ(p^ρ − p^{1−ρ}) =
−(p^ρ − p^{1−ρ})`. (G) `∏A = ±b` is fixed by `c`, which multiplies it by `(−1)^{Σ|U_t|}`;
a sum is even iff its number of odd terms is. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| A | `TheReflectionRadicalsOfOneHeightCarryTheParityOfItsZeros` | `primeUpperFibre`, `mem_primeUpperFibre`, `xiZeroMirror`, `prod_primeUpperFibre_mirror`, `primeHeightReflectionProduct`, `primeTraceConjugation_reflectionDifference`, `primeTraceConjugation_heightReflectionProduct` |
| B | same | `primeReflectionSquare`, `primeReflectionSquare_reflect`, `heightReflectionProduct_mul_self`, `heightReflectionProduct_map_mul_self`, `heightReflectionProduct_map`, `heightReflectionProduct_mul_self_mem` |
| C | same | `odd_card_primeUpperFibre_iff` |
| D | same | `reflectionDifference_ne_zero_of_ne`, `exists_prime_heightReflectionProduct_ne_zero` |
| E | same | `heightReflectionProduct_eq_zero_of_mem`, `exists_prime_radicand_product_not_square` |
| F | same | `lift_heightReflectionProduct` |
| G | `ASquareRelationAmongHeightRadicandsHasAnEvenNumberOfCriticalHeights` | `even_card_critical_of_isSquare` |

## Open

A source restriction that separates a lift of `r` from `c`: every class computed here is shared
by `c` and any lift.
