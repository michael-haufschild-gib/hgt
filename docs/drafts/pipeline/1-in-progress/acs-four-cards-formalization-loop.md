# ACS four-card formalization loop

- **ID:** acs-four-cards-loop
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** Formalize every claim of the four cards in docs/drafts/pipeline/2-fully-proven/acs and move them to 3-formalized.

## Cards and Lean coverage
| Card | Status |
|---|---|
| acs-pvc-cancellation-on-square-multiple-cofactors | all claims in Lean (TheClippedSquareComplement, OppositePrimeSignalsOnSquareMultiples); final audit pending |
| acs-pvc-first-primes-beyond-the-conductor | gap: first-prime power fragments only for a ≤ 19/10 (card: 12/7 ≤ a < 2); interval-length identity for the continuous prime mass; rest in Lean; final audit pending |
| acs-pvc-interior-shell-at-seven-fourths | all claims in Lean (InteriorProductShells horizonPair_bound = per-pair third difference; TheSevenFourthsConductorShell; TheSeventeenNinthsConductorPrefix); final audit pending |
| acs-pvc-the-quadratic-product-divider | gap: explicit ±c N^(34/9)/2 leading terms at the fixed cut, pole cancellation corollary, public O(n²) discrepancy + analyticity on Re s > 3; rest in Lean; final audit pending |

## Final audit list (one foreground compile each)
Pending: all.

## Log
- 2026-11-20 — loop resumed; coverage mapped.
