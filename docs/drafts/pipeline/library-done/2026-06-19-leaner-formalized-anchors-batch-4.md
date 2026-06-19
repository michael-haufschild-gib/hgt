# Library update request — Leaner formalized anchor batch 4

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-4
- **Stage:** library-backlog
- **Type:** LEDGER-UPDATE
- **Owner:** librarian
- **Source:** Leaner formalization pass over `docs/drafts/pipeline/2-fully-proven`

## Requested Update
Please update the shared status/index ledgers to reflect these `3-formalized` cards:

- `bounded-smooth-frequency-dictionary.md` added as a formalized split from `friable-dirichlet-auxiliary.md`; Lean definitions/theorems `boundedExponentVectorEquivSmooth` and `primeProduct_isBoundedSmooth_iff`.
- `diagonal-auxiliary-dirichlet-pullback.md` added as a formalized split from `friable-dirichlet-auxiliary.md`; Lean theorems `diagonalMonomial_eq_frequency` and `diagonalAuxiliaryForm_eq_dirichletPolynomial`.
- `natural-log-prime-factorization.md` added as a formalized split from `corank-transcendence-continuation-bridge.md`; Lean theorem `log_nat_eq_sum_factorization`.

The parent cards remain in `2-fully-proven` because their broader analytic/transcendence/corank claims are not fully Lean-formalized.

## Verification
Leaner checked theorem names by `/tmp` scratch file using `lake env lean` and `#print axioms`. Final verification for this batch is `lake build` plus `scripts/check_axioms.sh`; both should be reflected after this ticket is processed.

## Log
- 2026-06-19 — filed by Leaner to avoid direct edits to `docs/drafts/door/00-index.md` or `docs/drafts/door/00-status.md`.
