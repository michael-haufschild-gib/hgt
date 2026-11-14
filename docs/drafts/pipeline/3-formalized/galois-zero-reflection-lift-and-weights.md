# A lift of the reflection is conjugation exactly where the weight lies in `B`

- **ID:** gtz-reflection-lift-and-weights
- **Stage:** 3-formalized
- **Type:** THEOREM (reduction)
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, problems 2 and 3 (review-1411 §2.19).
- **Statement:** `B` the prime trace field, `G = Gal(E/B)`, `p` any prime.
  (A) `Re ρ = ½` iff `p^{2 Re ρ} ∈ B` and `σρ = 1 − ρ` for some `σ ∈ G`;
  (B) all zeros are critical iff the reflection lifts to `G` and `p^{2 Re ρ} ∈ B` for every zero;
  (C) if `σ ∈ G` lifts the reflection, `σρ = ρ̄` iff `p^{2 Re ρ} ∈ B`, and `σ` is conjugation iff
  every weight value lies in `B`;
  (D) if `σ` lifts the reflection, `cσ` acts as `ρ ↦ 1 − ρ̄`, fixes exactly the critical zeros,
  and RH holds iff `cσ = 1`.

## Goal

Problem 3 asks for the identification of a lift of `r` with conjugation. (C) says this
identification is exactly problem 2 (the weights). (B) splits RH into the two problems; neither
half alone gives RH (each is compatible with quartets: Q5). (D) is the arithmetic counterpart of
`cr ∈ G₊` on the heat cover.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

`ρ̄ = 1 − ρ` iff `Re ρ = ½` (`Im` agrees always). (A) ⇒: rational weight; `c` sends `ρ` to
`ρ̄ = 1 − ρ`. ⇐: a weight in `B` confines the orbit to `{ρ, ρ̄}`; `1 − ρ ≠ ρ` (imaginary parts),
so `1 − ρ = ρ̄`. (B) from (A) pointwise, with `c` as the lift under RH. (C) `σρ = 1 − ρ`; equality
with `ρ̄` is criticality, which is (A) given the lift. Faithfulness gives the global form.
(D) `cσρ = conj(1 − ρ) = 1 − ρ̄`, equal to `ρ` iff `Re ρ = ½`; faithfulness. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| A | `ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField` | `xiZeroConjEquiv_eq_reflect_iff`, `re_eq_half_iff_weight_mem_and_reflect` |
| B | same | `forall_re_eq_half_iff` |
| C | same | `lift_eq_conjugation_at_iff`, `lift_eq_conjugation_iff` |
| D | same | `conjugation_mul_lift_fixed_iff`, `forall_re_eq_half_iff_conjugation_mul_lift_eq_one` |

## Open

A source-derived statement for either half: the parity of the square relations among the
reflection radicands, or the membership `p^{2 Re ρ} ∈ B`.
