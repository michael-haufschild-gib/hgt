# Library update: Leaner formalized anchors batch 11

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-11
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update

Please update the shared door/status/index ledgers to reflect one new `3-formalized` card:

1. `docs/drafts/pipeline/3-formalized/additive-koszul-cocycle-skeleton.md`
   - Lean module: `formal/GaloisForLFunctions/KoszulCohomology.lean`
   - Lean anchors: `koszulD0_eq_zero_iff_invariant`, `koszulD1_eq_zero_iff_additiveCocycle`,
     `koszulCoboundary_cocycle`, `koszulD1_koszulD0_eq_zero`
   - Source: split from `docs/drafts/pipeline/2-fully-proven/multi-q-shafarevich-gluing-group.md` R0
   - Scope: exact additive first-Koszul cocycle/coboundary skeleton only.

Verification:
- Scratch name checks and `#print axioms` PASS for the cited Lean names.
- `cd formal && lake build` PASS.
- `bash scripts/check_axioms.sh` PASS, no `sorry`, 273 audited theorem outputs, allowed axiom subset only.

## Notes

The parent Shafarevich gluing ticket remains in `2-fully-proven` because the two-prime Shafarevich quotient,
nonabelian `H^1`, character-variety/Procesi input, and C5-star regularity are not fully Lean-formalized. The
Koszul Euler-characteristic lemmas in the Lean file were not banked in this card because they are not part of
the current source ticket's R0 claim.
