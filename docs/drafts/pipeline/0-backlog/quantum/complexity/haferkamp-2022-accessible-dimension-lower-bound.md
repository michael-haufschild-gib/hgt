# Haferkamp et al. 2022: accessible-dimension lower bound

- **ID:** haferkamp-2022-accessible-dimension-lower-bound
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached main paper, Proposition 1
- **Statement:** An architecture formed from `T` backwards-light-cone blocks of at most `L` gates has accessible dimension at least `T`, hence at least `R / L`.

## Goal

Formalize the Proposition 1 combination of the low-rank locus and Clifford high-rank point without weakening its architecture condition.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

Depends exactly on `haferkamp-2022-low-rank-locus` and `haferkamp-2022-clifford-light-cone-rank`.

## Log

- 2026-08-21 -- Extracted from attached main paper.
