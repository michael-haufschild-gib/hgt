# Haferkamp et al. 2022: contraction-map low-rank locus

- **ID:** haferkamp-2022-low-rank-locus
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached main paper, Lemma 1; attached supplement, Appendix B, Lemma 3
- **Statement:** For an `R`-gate architecture contraction map, the locus below its maximal differential rank is a closed algebraic measure-zero set; the maximal rank equals accessible dimension.

## Goal

Formalize the exact Lie-group contraction-map result, including the local-chart polynomial-minor argument and the rank-to-dimension equality.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

Reuse `MvPolynomialMatrixRankDefect` only for the polynomial-minor subclaim; it does not supply the required real algebraic measure or accessible-dimension layers.

## Log

- 2026-08-21 -- Extracted and cross-checked against the main paper.
