# Library update: Leaner formalized anchors batch 9

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-9
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update

Please update the shared door/status/index ledgers to reflect one new `3-formalized` card:

1. `docs/drafts/pipeline/3-formalized/vandermonde-initial-moment-core.md`
   - Lean module: `formal/GaloisForLFunctions/RHTower/ZeroEstimate.lean`
   - Lean anchors: `vandermonde_moments_eq_zero_of_injective`,
     `vandermonde_initial_moment_nonzero_of_nonzero_coeff`
   - Source: split from `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/zero-estimate-uniformity.md` part (a)
   - Scope: exact finite Vandermonde moment-determinacy lemma only.

Verification:
- `cd formal && lake build` PASS
- `bash scripts/check_axioms.sh` PASS, no `sorry`, 273 audited theorem outputs, allowed axiom subset only.

## Notes

The parent zero-estimate ticket remains in `2-fully-proven` because the analytic derivative wrapper,
determinant size estimate, Bohr support wrapper, and canonical-exhaustion/PNT uniformity bookkeeping are not
all formalized in one theorem.
