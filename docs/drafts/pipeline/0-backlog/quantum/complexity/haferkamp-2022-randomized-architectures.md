# Haferkamp et al. 2022: randomized-architecture corollary

- **ID:** haferkamp-2022-randomized-architectures
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached supplement, Appendix D, Corollary 1
- **Statement:** For every `alpha in [0,1)`, the paper's nearest-neighbour random `R`-gate circuit satisfies `Pr(Cu(U) >= alpha * (R / (9 n (n - 1)^2) - n / 3)) >= 1 - (n - 1) exp(-n) / (1 - alpha)`.

## Goal

Formalize the exact Bernoulli/Markov light-cone counting corollary and its reduction to Theorem 1.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

Depends on the main theorem plus finite-product probability inequalities.

## Log

- 2026-08-21 -- Extracted from attached supplement.
