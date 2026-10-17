# Origin concentration and exact energy continuity

- **ID:** infinite-grid-origin-energy-2026-10-17
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE
- **Scope:** Independent BiScaleUncertainty; proposed connected package 9.
- **Paper:** `docs/reports/BiScaleUncertainty/InfiniteGridOriginEnergy.md`

## Statement

For bounded-energy actual all-grid sources whose normalized correlations converge
uniformly, energy converges exactly when their singular energy is uniformly small
on a sufficiently short interval next to zero. No energy defect can occur away
from zero. Along an energy-convergent subsequence, every fixed origin interval
contains exactly the limiting kernel's energy there plus the entire defect.

## Plan and gates

- [x] Corpus search: `research 'uniform correlation convergence Levy energy origin uniform integrability energy defect' --mode deep --budget-seconds 90`.
  Discovery complete; source-only candidates, older-generation coverage, semantic coverage unmeasured.
- [x] Inspect actual source integrability, Fatou, interval splitting, and dominated convergence APIs.
- [x] Dependency-closed paper proof, including simultaneous correlation/energy subsequence extraction.
- [ ] Formalize tail stability, shrinking core, and exact continuity criterion.
- [ ] Formalize localization of every convergent energy defect.
- [ ] Direct leaf checks, complete axiom audit, umbrella/API wiring, formal lint.

## Boundary and next conjecture

No compact-source representation of a limiting kernel or polar closedness follows.
An actual strict-loss example is a separate next construction, not a premise:
normalize a compressed bump to raw energy one, so its mass is reciprocal normalized
energy and tends to zero. Add a translated copy inside the first grid gap to a fixed
source; the energy parallelogram selects a sign retaining one extra energy unit.
This construction is not certified here until its source geometry and uniform
correlation estimate are proved and formalized.

No numerical experiments, full builds, raised heartbeats, or unproved analytic interfaces.
