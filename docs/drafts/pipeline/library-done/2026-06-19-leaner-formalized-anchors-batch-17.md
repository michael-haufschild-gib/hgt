# Librarian handoff — Leaner formalized anchors batch 17

- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Type:** ledger/status update
- **Status:** pending

## Update requested
Record a new `3-formalized` Lean card:

- `docs/drafts/pipeline/3-formalized/bigraded-corank-tower-factorization.md`

## Lean anchors
- `formal/GaloisForLFunctions/BigradedCorank.lean`
- theorem `GaloisForLFunctions.algebraicIndependent_sumElim_intermediateField_iff`

## Source ticket
- `docs/drafts/pipeline/2-fully-proven/bigraded-corank-dss-cross.md` §G

## Scope note
This formalizes only the exact field-algebra tower law behind the §G factorization reduction. It does not formalize the concrete prime-log/Stieltjes families, infinite corank bookkeeping, Tannakian interpretation, or the exponential-period apex. The parent ticket remains in `2-fully-proven` with its broader 2 -> 3 gate still open.

## Verification
- Scratch `#check` and `#print axioms` passed for `algebraicIndependent_sumElim_intermediateField_iff`.
- `cd formal && lake build` passed.
- `bash scripts/check_axioms.sh` passed with the theorem added to the audited list: 274 theorem outputs; no real `sorry` tokens.
