# Cubic reciprocity at a common residue characteristic

- **ID:** cubic-reciprocity-common-characteristic
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [metaplectic Möbius descent](../1-in-progress/metaplectic-mobius-descent.md)
- **Statement:** For all Eisenstein primes `P,Q` away from three, primary generators `p,q` satisfy `χ_P(q)=χ_Q(p)`.

## Proof

Distinct residue characteristics are covered by the Frobenius argument.
For distinct `P,Q` above the same rational prime `ℓ`, put `t=−(p+q)`.
Since `λ²` divides three, `t` is primary. Neither `P` nor `Q` contains `t`:
otherwise one primary generator would belong to the other maximal ideal.

The ramification-inertia identity gives `Σ_R e_R f_R=2` above `ℓ`, with
each summand positive. Hence at most two primes lie above `ℓ`. Every prime
factor `R` of `t` therefore has residue characteristic different from `ℓ`.

Mathlib's cyclotomic PID theorem gives prime factorization. Replace each
factor by its primary generator. A primary unit is one, so the resulting
product equals `t` exactly. For every primary factor `r`, distinct-characteristic
reciprocity gives `χ_P(r)=χ_R(p)=χ_R(q)=χ_Q(r)`: modulo `R`, `p=−q`, and cubic
characters send minus one to one. Multiply over factors and reduce `t` modulo
`P,Q` to conclude. If `P=Q`, both symbols vanish.

## Lean

Module: `MetaplecticMobiusDescent/CubicReciprocityAtACommonCharacteristic.lean`.

- `exists_primary_prime_factorization`
- `maximal_eq_or_eq_of_same_residue_char`
- `cubic_reciprocity_primary`
- `primaryGenerator_reciprocity_all`

Direct `lake --old env lean` audit passed. All four transitive axiom audits
contain only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.

The auxiliary-factor argument is adapted from external OpenAI source
`GaussSum/SquarePhaseFactorization.lean`; attribution is in `NOTICE`.
Composite symbols and the Kubota multiplier remain separate obligations.
