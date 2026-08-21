# Haferkamp et al. 2022: semialgebraic image dimension

- **ID:** haferkamp-2022-semialgebraic-image-dimension
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached supplement, Appendix A, Lemma 2
- **Statement:** If `F : R^n -> R^m` is polynomial and `W` is a semialgebraic set of dimension `d`, then `F(W)` has dimension at most `d`.

## Goal

Formalize the paper's exact dimension monotonicity lemma, reusing rather than duplicating the completed stratification and image infrastructure.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

Direct dependency of Proposition 1 and Theorem 1.

## Log

- 2026-08-21 -- Extracted from attached supplement; no matching corpus declaration found.
