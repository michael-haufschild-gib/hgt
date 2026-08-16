# Library update: Leaner formalized anchors batch 8

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-8
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update

Please update the shared door/status/index ledgers to reflect one new `3-formalized` card:

1. `docs/drafts/pipeline/3-formalized/prime-log-height-bound.md`
   - Lean module: `formal/GaloisForLFunctions/RHTower/ZeroEstimate.lean`
   - Lean anchors: `primeLogHeight`, `logPrime_int_sum_eq_log_pos_sub_log_neg`, `logPrime_height_bound`
   - Source: split from `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/zero-estimate-uniformity.md` part (b)
   - Scope: exact S-free prime-log height inequality only.

Verification:
- `cd formal && lake build` PASS
- `bash scripts/check_axioms.sh` PASS, no `sorry`, 273 audited theorem outputs, allowed axiom subset only.

## Notes

The parent zero-estimate ticket remains in `2-fully-proven` because the determinant product size estimate,
Bohr support wrapper, and canonical-exhaustion/PNT uniformity bookkeeping are not fully Lean-formalized.
