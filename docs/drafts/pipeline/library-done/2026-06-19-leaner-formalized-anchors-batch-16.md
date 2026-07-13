# Library ledger update — Leaner formalized anchors batch 16

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-16
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update
Record the following new `3-formalized` card in the shared door/status/index ledgers:

- `docs/drafts/pipeline/3-formalized/adams-rankin-selberg-second-moment.md`

## Lean Certificate
- Lean module: `formal/GaloisForLFunctions/RHTower/AdamsOperations.lean`
- Definition/theorem anchors:
  - `adamsPowerSum`
  - `adamsPowerSum_tensor`
  - `adamsPowerSum_conj`
  - `adamsPowerSum_tensor_selfDual`
  - `adamsPowerSum_tensor_selfDual_normSq`
  - `adamsPowerSum_isobaricSum`
  - `adamsPowerSum_comp`
  - `adamsPowerSum_one`
  - `adams_secondMoment_weil_nonneg`
  - `satakeDet_tensor`
- Source cards: split from the Rankin-Selberg/`⊗`-power positivity references in `docs/drafts/pipeline/2-fully-proven/g5-over-fq-deligne-unitarity.md` §2-§3 and the prime-block positivity clause of `docs/drafts/pipeline/2-fully-proven/explicit-formula-as-constraint.md` §3.
- Scope: finite Satake-side Adams/Rankin-Selberg second-moment algebra only.

## Verification
- Scratch name check: PASS for all listed Adams anchors.
- Scratch axiom check: PASS; standard mathlib axioms only.
- `cd formal && lake build`: PASS.
- `bash scripts/check_axioms.sh`: PASS, no sorry; audit remains 273 theorem outputs.

## Notes
- Parent cards remain in `2-fully-proven`: Deligne positivity, global Rankin-Selberg theory, automorphic functoriality, explicit-formula transfer, prime averages, and zero-side period realization are not fully Lean-formalized.
