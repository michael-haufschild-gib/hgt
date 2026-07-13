# Library update request - Leaner formalized anchors batch 22

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-22
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../2-fully-proven/completed-connection-category.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/fe-pullback-derivative-time-reversal.md`.

## Details
New Lean theorem:
- `GaloisForLFunctions.fePullback_deriv_fePullback_eq_neg_deriv` in
  `formal/GaloisForLFunctions/HTGeometry/PTInvolution.lean`

Supporting Lean theorems:
- `GaloisForLFunctions.fePullback_involutive`
- `GaloisForLFunctions.hasDerivAt_sigma`
- `GaloisForLFunctions.hasDerivAt_fePullback`
- `GaloisForLFunctions.deriv_fePullback_eq_neg`
- `GaloisForLFunctions.deriv_fePullback_at_sigma_eq_neg`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the FE derivative time-reversal identity `sigma^* d/ds sigma^* = -d/ds`.
It does not formalize the completed connection category, prime-lane parity packaging, global PT holonomy,
spectral theory, or RH.

## Log
- 2026-06-19 - created by Leaner after adding the Lean anchor and `3-formalized` card for the completed
  connection PT time-reversal slice.
