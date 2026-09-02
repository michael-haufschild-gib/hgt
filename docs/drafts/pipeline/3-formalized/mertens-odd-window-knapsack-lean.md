# Mertens as a top-window odd sum and as the Euler characteristic of the squarefree knapsack complex

- **ID:** INT-LEAN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** no-go closure of `5-failed/integrality-anchor-law.md`
- **Statement:** `∑_{n ≤ x} μ(n) = ∑_{n ∈ (x/2, x], n odd} μ(n)`; `∑_{n ≤ x} μ(n) = ∑_S (−1)^{|S|}`
  over finite sets `S` of primes with `∏ S ≤ x` (faces of the squarefree knapsack complex);
  every window `(x/2, x]`, `x ≥ 3`, contains an odd prime; the affine map `s ↦ a s + b`
  preserves `(Re ρ − ½)` measured in strip widths.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.MertensOddWindowKnapsack` | `moebius_two_mul`, `sum_moebius_eq_sum_odd_window`, `primeSets`, `sum_primeSets_neg_one_pow`, `exists_odd_prime_window`, `relativeDisplacement_affine` |

Inputs reused: `RHTower.GibbsGas.squarefree_prod_primes`,
`RHTower.Sieve.moebius_eq_neg_one_pow_card_primeFactors`, mathlib `Nat.primeFactors_prod`,
`Nat.prod_primeFactors_of_squarefree`, `Nat.exists_prime_lt_and_le_two_mul`. Axioms:
`propext, Classical.choice, Quot.sound`.

## Log
- 2026-09-02 — created at stage 3.
