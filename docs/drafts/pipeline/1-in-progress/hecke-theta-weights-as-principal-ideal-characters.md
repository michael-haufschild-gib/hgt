# Hecke theta weights equal principal-ideal character values

- **ID:** hecke-theta-weights-as-principal-ideal-characters
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Hecke archimedean Mellin integrals](hecke-archimedean-mellin-integrals.md)
- **Statement:** For every nonzero algebraic integer, its finite theta weight times the actual real sign character equals its principal-ideal Hecke value, including the noncoprime zero case.

## Dependency-closed proof to formalize

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

All named inputs have been source-checked in the existing corpus. No Lean
proof of this bridge is yet claimed.

`/tmp/HeckePrincipalThetaWeightScratch.lean` contains the complete proposed
coefficient bridge and is awaiting its first compile. It also proves the
sign/magnitude decomposition of every nonzero real embedding and the full
actual real monomial. The chosen-generator corollary proves its field
nonvanishing internally using `inverseClassGenerator_mem_ne_zero`; it does
not retain a generator nonvanishing premise.
