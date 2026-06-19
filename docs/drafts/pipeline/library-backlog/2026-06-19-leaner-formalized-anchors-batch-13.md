# Library ledger update — Leaner formalized anchors batch 13

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-13
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update
Record the following new `3-formalized` card in the shared door/status/index ledgers:

- `docs/drafts/pipeline/3-formalized/local-factor-self-duality.md`

## Lean Certificate
- Lean module: `formal/GaloisForLFunctions/LocalFactorDuality.lean`
- Theorem anchor: `selfDual_localFactor_eq`
- Source card: split from `docs/drafts/pipeline/2-fully-proven/orthogonality-meta-theorem.md` §5.
- Scope: finite inversion-closed Satake multiset local-factor self-duality only.

## Verification
- Scratch name check: PASS for `GaloisForLFunctions.selfDual_localFactor_eq`.
- Scratch axiom check: PASS; standard mathlib axioms only.
- `cd formal && lake build`: PASS.
- `bash scripts/check_axioms.sh`: PASS, no sorry; audit remains 273 theorem outputs.

## Notes
- Leaner also corrected the metadata header of `docs/drafts/pipeline/2-fully-proven/orthogonality-meta-theorem.md` from `1-in-progress` to `2-fully-proven`, matching its folder and gate history.
- The parent `orthogonality-meta-theorem` card remains in `2-fully-proven`: the polarization lemma, Weil positivity import, realization-family scope, and universal orthogonality residual are not fully Lean-formalized.
