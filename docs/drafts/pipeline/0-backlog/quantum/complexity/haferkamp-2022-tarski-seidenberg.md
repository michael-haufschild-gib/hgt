# Haferkamp et al. 2022: Tarski--Seidenberg image theorem

- **ID:** haferkamp-2022-tarski-seidenberg
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached supplement, Appendix A, Theorem 2
- **Statement:** The image of every semialgebraic subset of `R^n` under every polynomial map `R^n -> R^m` is semialgebraic.

## Goal

Formalize the exact real polynomial-image theorem and the definitions it needs, without an o-minimality or quantifier-elimination axiom.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

Dependency of the main theorem; choose a constructive real-closed-field elimination proof only after paper-level dependency closure.

## Log

- 2026-08-21 -- Extracted from attached supplement; no matching corpus declaration found.
