# AAL: conjecture loop for an unconditional decision

- **ID:** aal-proof-conjecture-loop-2026-11-07
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-0711/aal.md
- **Statement:** `RHTower.AsymptoticAbscissaLaw` holds (or fails) for the Riemann zeta function, unconditionally.

## Goal
A dependency-closed proof or disproof of AAL, formalized in Lean with its corollaries (under AAL:
RH ⇔ ZAL ⇔ finite off-line support, collapse atlas `riemannHypothesis_tfae_of_asymptoticAbscissaLaw`).

## Gates
- [x] 0 → 1  in-progress: statement and reductions read in Lean (see logs/aal-report-research.md)
- [ ] 1 → 2  fully-proven: complete paper proof, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, axiom audit

## Approach
Conjecture loop over mechanisms that couple the bounded-height top layer to all heights and use
an input failing on every model of report §6.1. Working log: logs/aal-proof-loop-2026-11-07.md.

## Current state
No decision. Candidate mechanisms and their failures are listed in the working log.

## Log
- 2026-11-07 — created in 1-in-progress
