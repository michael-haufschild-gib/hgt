# Library update request — Leaner formalized anchor batch 5

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-5
- **Stage:** library-backlog
- **Type:** LEDGER-UPDATE
- **Owner:** librarian
- **Source:** Leaner formalization pass over `docs/drafts/pipeline/2-fully-proven`

## Requested Update
Please update the shared status/index ledgers to reflect these `3-formalized` cards:

- `local-euler-factor-q-difference.md` added as a formalized split from `c6-specialization-functors.md` / `multiplier-dichotomy-theorem.md`; Lean theorems `localEulerFactor_dilation_relation`, `localEulerFactor_q_difference`, and `localEulerFactor_prime_dilation_difference`.
- `finite-prime-log-annihilator.md` added as a formalized split from `holonomicity-limit-nonclosure.md` / `corank-seam-invariant.md`; Lean theorems `logPrime_diagonalResonant_eq_zero`, `primeLog_diagonalRelationLattice_eq_singleton`, and `finitePrimeLogAnnihilator_eq_singleton`.

The parent cards remain in `2-fully-proven` because their broader category/functor/corank-realization claims are not fully Lean-formalized.

## Verification
Leaner checked theorem names by `/tmp` scratch file using `lake env lean` and `#print axioms`. Final verification for this batch is `lake build` plus `scripts/check_axioms.sh`; both should be reflected after this ticket is processed.

## Log
- 2026-06-19 — filed by Leaner to avoid direct edits to `docs/drafts/door/00-index.md` or `docs/drafts/door/00-status.md`.
