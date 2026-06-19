# Library update request - Leaner formalized anchors batch 23

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-23
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../2-fully-proven/completed-base-archimedean-coordinate.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/finite-bohr-product-formula-scale.md`.

## Details
New Lean theorem:
- `GaloisForLFunctions.bohrCharacter_archimedeanSquareScale` in
  `formal/GaloisForLFunctions/BohrGenerators.lean`

Supporting Lean theorem:
- `GaloisForLFunctions.bohrCharacter_scaleAllCoordinates`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the finite-support Bohr-character scaling identity for applying `x_p -> p^-2 x_p`
on all prime coordinates. It does not formalize the Gamma symbol, digamma recurrence, `R+`, infinite
products, or the full completed-base construction.

## Log
- 2026-06-19 - created by Leaner after adding the Lean anchor and `3-formalized` card for the completed-base
  product-formula scale slice.
