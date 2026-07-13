# Library update request - Leaner formalized anchors batch 24

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-24
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../2-fully-proven/per-place-source-a-gamma-carriers.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/morita-gamma-finite-recurrence.md`.

## Details
New Lean theorem:
- `GaloisForLFunctions.moritaGammaFinite_succ` in
  `formal/GaloisForLFunctions/HTGeometry/MoritaGamma.lean`

Supporting Lean theorems:
- `GaloisForLFunctions.moritaGammaProduct_succ_of_dvd`
- `GaloisForLFunctions.moritaGammaProduct_succ_of_not_dvd`
- `GaloisForLFunctions.moritaGammaFinite_succ_of_dvd`
- `GaloisForLFunctions.moritaGammaFinite_succ_of_not_dvd`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the finite positive-integer Morita recurrence. It does not formalize p-adic analytic
continuation, the Source-A grade, the multiplier-dichotomy application, the uniform per-place `Gamma_v`
family, or the complex/p-adic comparison.

## Log
- 2026-06-19 - created by Leaner after adding the Lean anchor and `3-formalized` card for the finite Morita
  gamma recurrence.
