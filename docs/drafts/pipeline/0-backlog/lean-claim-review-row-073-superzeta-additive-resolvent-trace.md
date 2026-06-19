# Lean claim review row #73 — superzeta as additive resolvent trace

- **ID:** lean-claim-review-row-073-superzeta-additive-resolvent-trace
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #73; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** the superzeta is the additive resolvent trace, using a sum rather than a product.

## Goal
Audit the claim from scratch. Researchers first verify the finite formal statement, its relation to the named superzeta object, and the exact Sigma-versus-product content. Leaner checks formalization after that review.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/SuperzetaResolvent.lean`
- Candidate names: `superzeta_eq_sum_resolvent`, `superzeta_coeff_eq_powerSum`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; exact finite power-series/resolvent statement fixed
- [ ] 1 -> 2 fully-proven: researchers confirm a complete paper proof and identify any gap between finite resolvent algebra and the corpus-level superzeta claim
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Check the geometric-series identity, sum over a finite spectrum, and compare coefficients with power sums. Keep the analytic/infinite superzeta interpretation out of scope unless researchers explicitly prove it.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
