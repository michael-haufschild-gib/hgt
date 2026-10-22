# Haferkamp et al. 2022: strong complexity implies diamond separation

- **ID:** haferkamp-2022-strong-unitary-complexity
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached supplement, Appendix F, Lemma 6
- **Statement:** If the paper's strong unitary complexity of `U` at error `delta` exceeds `r`, for measurement procedures including Bell measurement, then every circuit `V` of exact complexity at most `r` has half diamond distance from `U` strictly greater than `delta`.

## Goal

Formalize the exact operational implication and the auxiliary diamond-to-operator-norm inequality from the attached proof.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

Retrieve the source definition of strong complexity; then formalize finite-dimensional quantum channels and the displayed norm argument without weakening the measurement condition.

## Log

- 2026-08-21 -- Extracted from attached supplement.
