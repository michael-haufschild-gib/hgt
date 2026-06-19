# Library update request — Leaner formalized anchor batch 2

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-2
- **Stage:** library-backlog
- **Type:** LEDGER-UPDATE
- **Owner:** librarian
- **Source:** Leaner formalization pass over `docs/drafts/pipeline/2-fully-proven`

## Requested Update
Please update the shared status/index ledgers to reflect these `3-formalized` cards:

- `lean-claim-review-row-001-log-prime-linear-independence.md` moved from `2-fully-proven` to `3-formalized`; Lean theorem `linearIndependent_log_primes` proves the stated `ℚ`-linear independence, with `logPrime_linearIndependent_int` and `logPrime_no_rat_relation` as companion forms.
- `exponential-sum-order-bound.md` added as a formalized split from `zero-estimate-uniformity.md`; Lean theorem `exponentialSum_has_nonzero_iteratedDeriv_lt_card`.
- `cc-gauge-trivialization-identity.md` added as a formalized split from `multiplier-dichotomy-theorem.md`; Lean theorems `ccGaugeMultiplier_eq_const` and `hasDerivAt_mul_exp_const_ode`.
- `prime-dilation-no-fixed-torus-point.md` added as a formalized split from `multi-q-shafarevich-gluing-group.md`; Lean theorems `primeDilation_fixed_eq_zero`, `primeDilation_no_fixed_unit`, and `no_primeDilation_fixed_torus_point`.
- `archimedean-shift-diagonal-prime-lanes.md` added as a formalized split from the archimedean/prime-lane cards; Lean theorems `primeDiagonal_shift_apply` and `primeDiagonal_shift`.

## Verification
Leaner checked theorem names by `/tmp` scratch file using `lake env lean` and `#print axioms`. The final verification command set for this batch is `lake build` plus `scripts/check_axioms.sh`; both should be reflected in the ledger after this ticket is processed.

## Log
- 2026-06-19 — filed by Leaner to avoid direct edits to `docs/drafts/door/00-index.md` or `docs/drafts/door/00-status.md`.
