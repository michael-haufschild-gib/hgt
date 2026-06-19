# Library ledger update — Leaner formalized anchors batch 15

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-15
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update
Record the following new `3-formalized` card in the shared door/status/index ledgers:

- `docs/drafts/pipeline/3-formalized/satake-tensor-local-factor.md`

## Lean Certificate
- Lean module: `formal/GaloisForLFunctions/SatakeTensor.lean`
- Definition/theorem anchors:
  - `satakeTensorParameters`
  - `satakeLocalFactor`
  - `satakeTensor_diagonal`
  - `satakeLocalFactor_tensor`
- Source cards: split from `docs/drafts/pipeline/2-fully-proven/g4-over-fq-deligne-katz.md` §1, `docs/drafts/pipeline/2-fully-proven/c6-specialization-functors.md` §2, and the function-field `⊗`/tensor-of-sheaves recovery.
- Scope: finite diagonal Satake tensor-product and local-factor double-product algebra only.

## Verification
- Scratch name check: PASS for the Satake tensor definitions/theorems.
- Scratch axiom check: PASS for `satakeTensor_diagonal` and `satakeLocalFactor_tensor`; standard mathlib axioms only.
- `cd formal && lake build`: PASS.
- `bash scripts/check_axioms.sh`: PASS, no sorry; audit remains 273 theorem outputs.

## Notes
- Parent cards remain in `2-fully-proven`: sheaf-level tensor functoriality, Deligne-Katz monodromy, global Rankin-Selberg/functoriality, and analytic continuation are not fully Lean-formalized.
