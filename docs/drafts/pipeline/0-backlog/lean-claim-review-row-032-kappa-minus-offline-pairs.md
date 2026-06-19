# Lean claim review row #32 — exact `kappa_-` count for finite carriers

- **ID:** lean-claim-review-row-032-kappa-minus-offline-pairs
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #32; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** `kappa_-` equals the number of off-line zero-pairs exactly, for the finite carrier.

## Goal
Audit the claim from scratch. Researchers first verify the finite-carrier mathematical theorem, including hypotheses and exact notion of negative inertia. Leaner checks the claimed formalization only after that review.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/CarrierCauchy.lean`
- Candidate names: `multiPair_carrier_exact_neg_inertia`, `multiPair_carrier_linearIndependent`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; finite-carrier hypotheses and inertia convention fixed
- [ ] 1 -> 2 fully-proven: researchers confirm a complete paper proof from scratch, including exact lower and upper bounds
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Review the finite Pick matrix / carrier model, isolate the off-line conjugate-pair contribution, and check that the linear independence hypotheses are sufficient for exact negative inertia.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
