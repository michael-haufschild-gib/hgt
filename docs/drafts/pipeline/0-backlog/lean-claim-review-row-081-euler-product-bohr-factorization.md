# Lean claim review row #81 — Euler product and Bohr factorization

- **ID:** lean-claim-review-row-081-euler-product-bohr-factorization
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #81; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** First Theorem: Euler product iff Bohr factorization, as a fake filter.

## Goal
Audit the claim from scratch. Researchers first verify the exact arithmetic-function statement and whether the Lean theorem proves the claimed iff or only a finite/factorization proxy. Leaner checks formalization after the paper review.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/EulerProduct.lean`
- Candidate names: `isMultiplicative_iff_bohr_factorization`, `fake_fails_factorization`, `davenportHeilbronnFakeCoeff_not_isMultiplicative`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; exact arithmetic-function and Bohr-lift definitions fixed
- [ ] 1 -> 2 fully-proven: researchers confirm a complete paper proof and the fake-filter consequence
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Check the equivalence between multiplicativity/Euler product data and factorization of the Bohr lift. Then review the explicit fake coefficient witness as a separate corollary.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
