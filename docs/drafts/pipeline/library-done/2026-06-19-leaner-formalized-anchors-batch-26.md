# Library update request - Leaner formalized anchors batch 26

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-26
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../2-fully-proven/archimedean-generator-axis-mode.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/two-axis-bohr-combination-mode.md`.

## Details
New Lean theorems in `formal/GaloisForLFunctions/BohrGenerators.lean`:
- `GaloisForLFunctions.twoAxisMode_support_eq`
- `GaloisForLFunctions.bohrCharacter_twoAxis_product`
- `GaloisForLFunctions.twoAxisMode_ne_zero`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the finite support/product algebra showing that a ring product of two distinct
nonzero axis Bohr characters is a genuine two-axis combination mode. It does not formalize the analytic
`partial_s` operator, infinite torus generator domains, digamma residue, or the C5-localization synthesis.

## Log
- 2026-06-19 - created by Leaner after adding the Lean anchor and `3-formalized` card for the two-axis Bohr
  combination mode.
