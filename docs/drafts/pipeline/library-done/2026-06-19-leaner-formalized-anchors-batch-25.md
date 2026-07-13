# Library update request - Leaner formalized anchors batch 25

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-25
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../2-fully-proven/family-dss-gsh.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/family-cross-resonance-modulus-split.md`.

## Details
New Lean theorem:
- `GaloisForLFunctions.familyTwistedProduct_split` in
  `formal/GaloisForLFunctions/HTGeometry/FamilyCrossResonance.lean`

Supporting Lean theorems:
- `GaloisForLFunctions.bohrCharacter_finset_sum`
- `GaloisForLFunctions.bohrCharacter_familyExponentSum`
- `GaloisForLFunctions.familyPrimeBalance_eq_zero_of_primeProduct_eq`
- `GaloisForLFunctions.familyPrimeBalance_apply_eq_zero_of_primeProduct_eq`
- `GaloisForLFunctions.familyPrimeBalance_eq_zero_of_primeLogFrequency_eq_zero`
- `GaloisForLFunctions.familyPrimeBalance_apply_eq_zero_of_primeLogFrequency_eq_zero`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the finite product split and unique-factorization modulus balance for shared prime
scales. It does not formalize Dirichlet characters, finite cyclotomic Galois theory, GSH, zero statistics,
or the A2/F1 value-lift layer.

## Log
- 2026-06-19 - created by Leaner after adding the Lean anchor and `3-formalized` card for the family
  cross-resonance modulus split.
