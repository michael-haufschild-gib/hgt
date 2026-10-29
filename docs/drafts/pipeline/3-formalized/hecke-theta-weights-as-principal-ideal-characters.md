# Hecke theta weights equal principal-ideal character values

- **ID:** hecke-theta-weights-as-principal-ideal-characters
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke archimedean Mellin integrals](hecke-archimedean-mellin-integrals.md)
- **Statement:** For every nonzero algebraic integer, its finite theta weight times the actual real sign character equals its principal-ideal Hecke value, including the noncoprime zero case.

## Proof

When the residue is a unit, `not_mem_of_isUnit_mk` excludes every bad prime.
`mk0_mem_primeToUnits` constructs its actual prime-to field unit.
`idealUnit_span_eq` identifies the principal ideal, and
`rayHom_algebraMap` identifies reduction and signs. Apply the proved
`character_rayClassOfElt_eq` and `finiteHeckeWeight_unit`.

When the residue is not a unit, the finite theta weight is zero. If the
principal ideal belonged to the prime-to ideal group, its field generator
would belong to `primeToUnits`. Its valuation would equal one at every bad
prime. The integral valuation membership criterion then excludes all these
primes from the generator, contradicting noninvertibility of its residue
by `isUnit_mk_of_forall_not_mem`. Thus the ideal Hecke value is also zero.

Finally `infiniteSignCharacter_eq_prod` converts the actual infinite
character to the parity-sign product. Applied to the chosen inverse-class
generator, `span_inverseClassGenerator` and `heckeValue_mul` identify the
coefficient with `heckeValue(I)*heckeValue(b)` without a coprimality premise.

## Lean verification

Module: `HeckeLFunctions/HeckeThetaWeightsArePrincipalIdealCharacters.lean`.

- `real_embedding_eq_sign_mul_place` and
  `heckeRealMonomial_eq_sign_mul_placeProduct` split real embeddings into
  their actual sign character and positive place magnitudes.
- `integralHeckeWeight_mul_infiniteSign_eq_heckeValue` and
  `integralHeckeWeight_mul_parities_eq_heckeValue` prove the principal-ideal
  coefficient identity, including the noncoprime zero case.
- `inverseClassGenerator_ne_zero_in_field` proves the actual chosen
  generator's nonvanishing.
- `inverseClassGenerator_heckeCoefficient` identifies the class coefficient
  as `heckeValue(I)*heckeValue(b)`.

Three transitive axiom audits returned only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit passed without warnings:
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeThetaWeightsArePrincipalIdealCharacters.lean`.
Wired into the Hecke umbrella; umbrella not compiled.
