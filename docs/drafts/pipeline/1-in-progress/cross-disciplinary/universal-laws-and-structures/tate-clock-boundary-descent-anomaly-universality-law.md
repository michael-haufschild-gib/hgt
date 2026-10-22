# Tate-clock boundary descent-anomaly universality law

## Status

- Stage: 1-in-progress
- Lean target: `GaloisForLFunctions.HTGeometry.TateClockBoundaryDescentAnomalyUniversalityLaw`

## Theorem-generated route

Source statements were read before synthesis:

- `clockDescentAnomaly_comp_constraint`
- `tateClockInd_boundaryInterval_add_forwardN_backwardN`
- `tateClockIndBoundaryInterval_add`
- `tateClockIndBoundaryInterval_eq_zero_iff_mem_tailSubmodule`
- `mem_tateClockIndTailSubmodule_iff_exists_forwardN`

The shared endomorphism is `m`-step forward-after-backward tail reconstruction.  Comparing it to
the identity through `clockDescentAnomaly` produces exactly the oriented boundary interval.  The
existing tail and range classifications therefore become the kernel classification of this same
anomaly, and interval addition becomes its explicit cocycle law.

## Candidate law

At every depth, Tate-clock boundary charge is precisely descent anomaly; anomaly-free states are
exactly forward-reconstructible tails; and adding depths composes boundary anomalies by the
oriented interval cocycle.

## Open audits

- Exact Lean check
- Axiom audit
- Literature novelty audit
