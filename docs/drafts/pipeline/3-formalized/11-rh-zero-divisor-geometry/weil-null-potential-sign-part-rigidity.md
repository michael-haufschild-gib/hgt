# Annihilators of the Weil cone have unbounded block mass on both sides

- **ID:** weil-null-potential-sign-part-rigidity
- **Stage:** 3-formalized (Lean, unconditional, standard axioms)
- **Type:** THEOREM (Lean)
- **Context:** template (d), uniqueness U in its Gordan-dual form.
  - The C-PIN certificate is a prime-blind `ν = Ξ²ĥ` with `ĥ > 0` (big-picture card, rows 484–486).
  - Its obstruction is an *annihilator*: a log-bounded `u`, with `u(0) = u(1) = 0`, whose null potential `ψ_u(y) = Σ_n u(n)(K(y+log n) + K(y−log n))` is positive definite. Equivalently, `Ξ²·Σ u(n)2cos(t log n) ≥ 0`.
  - Already excluded in the corpus: one-signed `u` (`WeilNullPotentialOneSidedWitness`) and log-summable `u` (`WeilLogSummableRigidity`, `WeilAbscissaRigidity`). Mixed-sign elimination was open.

## Statement
If either sign part of an annihilator has bounded mass on the logarithmic blocks `{n : ⌊log n⌋ = j}`, uniformly in `j`, then the annihilator is `0`. In particular, a summable sign part forces `u = 0`.

So any nonzero annihilator, and hence any obstruction to C-PIN, needs unbounded block mass in both its positive and its negative part. Its smoothed signed block sums stay bounded, because `|ψ_u| ≤ ψ_u(0)`. It must therefore be a "locally balanced" sequence with large cancelling blocks.

## Proof
1. Positive definiteness gives `|ψ_u(y)| ≤ ψ_u(0)` for every `y`.
2. Split `ψ_u = ψ_{u⁺} − ψ_{u⁻}`.
3. If `u⁻` has block mass `≤ B`, then `ψ_{u⁻} ≤ 6Ce²B`. This uses `K(z) ≤ Ce^{−2|z|}`, `|y ± log n| ≥ ||y| − log n|`, block grouping, and `Σ_j e^{−2|x−j|} ≤ 3` (two geometric tails with ratio `e^{−2} ≤ 1/3`).
4. So `ψ_{u⁺}(y) ≤ ψ_u(0) + 6Ce²B` for all `y`.
5. `K ≥ m > 0` on `[−1, 1]`, and evaluation at the block centre `j + ½` gives block mass of `u⁺` at most `(ψ_u(0) + 6Ce²B)/m`. The `u⁺` case is symmetric, via `ψ_u ≥ −ψ_u(0)`.
6. Hence `|u| = u⁺ + u⁻` has bounded blocks, so `Σ|u(n)|n^{−1/4} < ∞`.
7. Absolute-abscissa rigidity for positive-definite null potentials at `σ = 1/4 < ½` gives `u = 0`.

## Lean
Module `RHTower/WeilNullPotentialSignPartRigidity` (namespace `RHTower.WeilAbscissa`), wired after `WeilNullPotentialOneSidedWitness`. Axioms `[propext, Classical.choice, Quot.sound]`; zero messages.

| Claim | Declaration |
|-|-|
| sign parts, `ψ_u = ψ_{u⁺} − ψ_{u⁻}` | `posPart`, `negPart`, `nullPotential_eq_sub` |
| bounded potential of a summable / block-bounded part | `nullPotential_le_of_summable`, `nullPotential_le_of_block`, `sum_exp_neg_two_abs_le` |
| window lower bound, block centre | `mul_sum_le_nullPotential`, `abs_block_center_sub_log_le` |
| blocks ⇒ `Σ|u|n^{−1/4} < ∞` | `summable_rpow_of_block_le`, `eq_zero_of_blocks` |
| **Main theorems** | `eq_zero_of_positiveDefinite_nullPotential_of_negPart_block`, `…_posPart_block`, `…_summable_negPart`, `…_summable_posPart` |

## Scope
This is not RH: it narrows the crystalline core of U. The general mixed-sign annihilator question remains open, now restricted to sequences whose positive and negative parts both have unbounded logarithmic-block mass while their `K`-smoothed signed block sums stay bounded.

## Log
- 2026-10-07 (loop row 544): proved and formalized.
