# Haferkamp et al. 2022: weighted circuit complexity equals `C1`

- **ID:** haferkamp-2022-weighted-complexity-cost
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached supplement, Appendix F, Lemma 5
- **Statement:** For every integer `n` and `U in SU(2^n)`, weighted two-local circuit complexity `Cw(U)` equals the `C1(U)` control cost.

## Goal

Formalize the exact equality after dependency-closing the paper's cited Trotter/control argument.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

This is asserted with a proof sketch only; retrieve the primary source and fix all control-regularity and Trotter-limit conventions before Lean.

## Log

- 2026-08-21 -- Extracted from attached supplement.
