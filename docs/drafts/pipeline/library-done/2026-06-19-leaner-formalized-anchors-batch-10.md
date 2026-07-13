# Library update: Leaner formalized anchors batch 10

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-10
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update

Please update the shared door/status/index ledgers to reflect one new `3-formalized` card:

1. `docs/drafts/pipeline/3-formalized/rank-one-scalar-cocycle-quotient.md`
   - Lean module: `formal/GaloisForLFunctions/HTGeometry/RankOneCohomology.lean`
   - Lean anchors: `scalarCocycle_mul`, `scalarCocycle_inv`, `rankOneCoboundary_cocycle`,
     `rankOneCoboundaryCocycle_mul`, `rankOneCoboundaryCocycle_inv`, `rankOnePicard_commGroup`
   - Source: split from `docs/drafts/pipeline/2-fully-proven/multi-q-shafarevich-gluing-group.md` R0
   - Scope: exact rank-one scalar cocycle/coboundary quotient skeleton only.

Verification:
- Scratch name checks and `#print axioms` PASS for the cited Lean names.
- `cd formal && lake build` PASS.
- `bash scripts/check_axioms.sh` PASS, no `sorry`, 273 audited theorem outputs, allowed axiom subset only.

## Notes

The parent Shafarevich gluing ticket remains in `2-fully-proven` because nonabelian `H^1`, the full
Shafarevich kernel, character-variety/Procesi input, and C5-star regularity are not fully Lean-formalized.
