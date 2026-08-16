# Library update request - Leaner formalized anchors batch 20

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-20
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../3-formalized/not_new_scientific_knowledge/universal-prime-side-orthogonality.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/fe-inversion-scale-bohr-coordinate.md`.

## Details
Existing Lean theorem:
- `GaloisForLFunctions.cpow_inversion_scale` in `formal/GaloisForLFunctions/Core.lean`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the FE coordinate identity `p^{-(1-s)} = p^{-1} * (p^{-s})^{-1}`. It does not
formalize torus representation categories, compact-form uniqueness, the general Satake quantifier, Weil
positivity, or RH.

## Log
- 2026-06-19 - created by Leaner after adding the `3-formalized` card for the existing audited Lean theorem.
