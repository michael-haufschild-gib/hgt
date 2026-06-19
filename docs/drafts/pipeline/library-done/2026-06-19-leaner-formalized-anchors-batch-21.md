# Library update request - Leaner formalized anchors batch 21

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-21
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../2-fully-proven/g5-over-fq-deligne-unitarity.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/function-field-weight-normalization.md`.

## Details
New Lean theorem:
- `GaloisForLFunctions.functionFieldWeightNormalize_norm_eq_one_iff` in
  `formal/GaloisForLFunctions/BoundaryModulus.lean`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the scalar weight-circle normalization
`|q^(-w*deg/2) alpha| = 1 iff |alpha| = q^(w*deg/2)`. It does not formalize Poincare duality, sheaves,
polarization, Deligne purity, `Fix(iota)`, or RH over `F_q`.

## Log
- 2026-06-19 - created by Leaner after adding the Lean anchor and `3-formalized` card for the scalar
  function-field G5 normalization step.
