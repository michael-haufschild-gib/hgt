# Haferkamp et al. 2022: approximate complexity versus `C2` cost

- **ID:** haferkamp-2022-approximate-complexity-cost
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached supplement, Appendix F, Theorem 4
- **Statement:** For every integer `n`, `U in SU(2^n)`, and `eta > 0`, approximate two-local circuit complexity is at most `c * C2(U)^3 * n^6 / eta^2` for the cited universal constant `c`.

## Goal

Formalize the cited exact quantitative cost-to-circuit theorem after its primary proof and constant convention are audited.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

This is a cited theorem, not proved in the attached paper; retrieve and audit its primary source before any formalization work.

## Log

- 2026-08-21 -- Extracted from attached supplement.
