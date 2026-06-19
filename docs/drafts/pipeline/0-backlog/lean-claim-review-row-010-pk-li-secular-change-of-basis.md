# Lean claim review row #10 — `P_k` closed form and Li/secular change of basis

- **ID:** lean-claim-review-row-010-pk-li-secular-change-of-basis
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #10; ../../door/bucket-ledger-footholds.md; dss-reduction-formalize.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** `P_k` closed form plus the Li <-> secular integer change-of-basis.

## Goal
Audit the claim from scratch. Researchers first decide whether the closed form and the triangular change-of-basis are valid, correctly scoped, and sufficient for the row. Leaner only checks formalization after that paper review.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/SecularMoments.lean`
- Candidate names: `li_secular_pointwise`, `secular_li_pointwise_inv`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; exact finite/infinite scope fixed; old ledger claim treated as unverified
- [ ] 1 -> 2 fully-proven: researchers confirm the paper proof and whether this row should be split into smaller statements
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Review the definitions of Li coefficients and secular/power-sum coordinates, prove both triangular transformations, and identify the ring and indexing conventions needed for a clean statement.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
