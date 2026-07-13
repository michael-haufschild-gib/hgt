# Library update request - Leaner formalized anchors batch 27

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-27
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../2-fully-proven/completed-base-archimedean-coordinate.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/finite-coordinate-scale-commutation.md`.

## Details
New Lean theorems in `formal/GaloisForLFunctions/HTGeometry/BohrGenerators.lean`:
- `GaloisForLFunctions.scaleCoordinate_commute`
- `GaloisForLFunctions.scaleAllCoordinates_commute`
- `GaloisForLFunctions.scaleCoordinate_scaleAllCoordinates_commute`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the finite coordinate-map commutation algebra for prime-coordinate scalings. It does
not formalize the Gamma symbol, digamma recurrence, analytic derivation `partial_s`, full
difference-differential ring `R+`, or the archimedean-symbol action.

## Log
- 2026-06-19 - created by Leaner after adding the Lean anchor and `3-formalized` card for finite
  coordinate-scale commutation.
