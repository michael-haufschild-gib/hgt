# Mass-shifted adaptive mixed source tail degree law

- **ID:** mass-shifted-source-tail-degree
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, (9.3.818)--(9.3.819)
- **Statement:** Adjacent source-action difference has exact full-tail integral equal to adjacent Jacobi alpha connector, whose cumulative-flux edge has finite `L²` capital.

## Goal

Replace unspecified inter-degree leakage by exact source plaquette and quantitative outgoing-ray
budget.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized: `XiShiftedCanonicalAdmissionAdaptiveMixedSourceTailDegreeLaw.lean`, targeted build green, standard-axiom audit
- [ ] 3 → 4 publication-ready

## Approach

Subtract exact fixed-degree tail source identities, use adjacent flux trace law, then dominate
squared connector by newborn source action.

## No-go closure

- **Exact killing theorem/mechanism:** pairwise budgets alone can accumulate with degree.
- **Strongest positive survivor:** exact tail plaquette and `L²` connector bound by `3/2` newborn entry flux.
- **New insight:** remaining leakage is degree-diagonal capital, not mass-tail integrability.
- **Status:** paper and Lean proofs dependency-closed; route novelty unverified.

## Log

- 2026-08-13 — formalized full-tail source difference and adjacent connector Dirichlet budget.
