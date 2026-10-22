# Haferkamp et al. 2022: probability-one linear state-complexity growth

- **ID:** haferkamp-2022-linear-state-complexity
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached main paper, Theorem 1 state conclusion; attached supplement, Appendix C
- **Statement:** Under the Theorem-1 random architecture hypotheses, exact state complexity of `U |0^n>` is at least `R / (9 L) - n / 3` with unit probability in the paper's state pre-saturation range `T < 2^(n + 1) - 1`.

## Goal

Formalize the exact state-map variant of the main result, including its separate real-dimension and independent computational-basis direction argument.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

Reuses the unitary proof only after separately formalizing Appendix C's map to the unit sphere and its `2^(n+1) - 1` independent state directions.

## Log

- 2026-08-21 -- Split from Theorem 1 to preserve one exact claim per card.
