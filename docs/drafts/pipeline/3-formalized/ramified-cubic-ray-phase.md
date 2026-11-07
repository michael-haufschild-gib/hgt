# Ramified cubic phases modulo nine

- **ID:** ramified-cubic-ray-phase
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every primary `p=1+3A+3Bω`, `(ω/p)₃=ω^(2A−B)`, `(λ/p)₃=ω^A`, and `(1+2ω/p)₃=ω^(−B)`. These phases depend only on `p mod 9`.

Define `Lᵤᵥ(p)=ω^(uA+vB)`. Multiplication of primary coordinates is addition
modulo three, so every `Lᵤᵥ` is multiplicative. Exact primary factorization
extends the prime supplementary laws to all primary denominators. The different
identity `1+2ω=−ωλ` gives its phase. Congruence modulo nine fixes `A,B mod 3`.

More generally, if primary `a,b` satisfy `9 | a−b` and `x | a−b`, then
`(x/a)₃=(x/b)₃`. Factor `x`. The six units are handled by the unit phase.
A prime away from three can be replaced by its primary associate; reciprocity
then turns the denominator change into numerator congruence. A prime above
three is associated to `λ` and is handled by its supplementary law.
Multiplicativity assembles the result. The zero numerator forces `a=b`.

Module: `MetaplecticMobiusDescent/TheRamifiedCubicPhaseLivesModuloNine.lean`.
Endpoints: `symbol_lambda_eq_linearRay`, `symbol_omega_eq_linearRay`,
`symbol_traceLambda_eq_linearRay`, `symbol_traceLambda_congr_mod_nine`,
`symbol_unit_congr_mod_nine`, `symbol_denominator_congr`.
Direct Lean audit passed. All six transitive axiom lists contain only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.

Adapted from external OpenAI `Reciprocity/RamifiedSymbol.lean`; attribution
and license are recorded in `NOTICE`. The matrix multiplier is recorded on
[cubic-jacobi-symbol-and-kubota-character](cubic-jacobi-symbol-and-kubota-character.md).
