# Library update request — Leaner formalized anchor batch 3

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-3
- **Stage:** library-backlog
- **Type:** LEDGER-UPDATE
- **Owner:** librarian
- **Source:** Leaner formalization pass over `docs/drafts/pipeline/2-fully-proven`

## Requested Update
Please update the shared status/index ledgers to reflect these `3-formalized` cards:

- `rank-one-diagonal-kernel-splitting.md` added as a formalized split from `multi-q-shafarevich-gluing-group.md`; Lean theorem `diagonalKer_mul_eq_sum_ker`.
- `monotone-natural-stabilization.md` added as a formalized split from `holonomicity-limit-nonclosure.md`; Lean theorem `monotoneNat_eventually_constant_of_bddAbove`.

The parent cards remain in `2-fully-proven` because their broader cohomology/corank-limit/category claims are not fully Lean-formalized.

## Verification
Leaner checked theorem names by `/tmp` scratch file using `lake env lean` and `#print axioms`. Final verification for this batch is `lake build` plus `scripts/check_axioms.sh`; both should be reflected after this ticket is processed.

## Log
- 2026-06-19 — filed by Leaner to avoid direct edits to `docs/drafts/door/00-index.md` or `docs/drafts/door/00-status.md`.
