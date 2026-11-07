# The cubic conversion phase lives modulo two

- **ID:** cubic-phase-modulo-two
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Products of sextic residue values at four equal a fixed cubic character of the primary product modulo two.

## Exact statement

Let `P_i` be Eisenstein primes away from two and three, with canonical primary
generators `p_i` and sextic characters `χ_i`. Put `p=∏p_i`. Then

`∏χ_i(4) = (p/(2))₃`.

The right side is evaluated in a fixed complex embedding. In particular, the
product equals one when `p≡1 mod 2`. For distinct primes and any additive
character `ψ` on the composite quotient, the exact conversion factor is

`c(I,ψ) = (p/(2))₃ N(I) / (p G₃(I,ψ))`.

Thus only the primary angular factor and quadratic Gauss phase remain beyond
the fixed cubic character.

## Proof

The generator `−2` is primary since `(ω−1)²=−3ω`. Its ideal has norm four.
Any maximal ideal above it has norm dividing four, greater than one, and
congruent to one modulo three because its residue field contains the three
cubic roots of unity. Its norm is therefore four. Containment and norm equality
show that `(2)` itself is maximal.

Since `4=(−2)²` and `χ_i²` is the cubic character, reciprocity at the distinct
residue characteristics gives `χ_i(4)=(p_i/(2))₃`. Multiplicativity assembles
the product. CRT factorization of the quadratic Gauss sum gives the displayed
conversion-factor formula.

## Lean and scope

Module: `MetaplecticMobiusDescent/TheCubicPhaseLivesModuloTwo.lean`.

- `Eisenstein.cubicTwoIdeal_isMaximal`
- `Eisenstein.complexSextic_four_eq_fixed_two`
- `Eisenstein.complexSextic_four_prod_eq_one`
- `Eisenstein.compositeConversionFactor_eq_rayFactor`

Direct `lake --old env lean` passed; four endpoint axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella import wired. The fixed-two
reciprocity specialization is adapted from the external OpenAI development;
source attribution and license accompany the module.

Quadratic Gauss-phase control modulo four and the theta/mean-square analysis
remain unproved here. No cancellation estimate follows from this theorem alone.
