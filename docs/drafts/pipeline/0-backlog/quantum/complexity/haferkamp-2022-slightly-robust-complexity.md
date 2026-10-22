# Haferkamp et al. 2022: slightly robust exact-complexity corollary

- **ID:** haferkamp-2022-slightly-robust-complexity
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached supplement, Appendix E, Corollary 2
- **Statement:** For each `delta in (0,1]`, a Theorem-1 random architecture has a positive architecture-and-`delta` dependent Frobenius separation from every circuit using at most `R / (9 L) - n / 3` gates, with probability at least `1 - delta`.

## Goal

Formalize the paper's compactness/finite-cover robustness corollary with its deliberately non-uniform positive separation.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

Depends on Theorem 1 and exact compact-metric separation; it must not be promoted into a uniform-error result.

## Log

- 2026-08-21 -- Extracted from attached supplement.
