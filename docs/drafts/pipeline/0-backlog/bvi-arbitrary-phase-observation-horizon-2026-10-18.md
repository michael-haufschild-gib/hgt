# Arbitrary-phase observation horizon

- **ID:** bvi-arbitrary-phase-observation-horizon
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** Contributions 005 and 007, exact initial and common-return kernels.
- **Statement:** For every `n,A:ℕ` and real weight `c`, with `N=n+3`, determine whether
  vanishing on `[A,A+2*n+2]` is equivalent to `sieveVariance N c=0`.

## Goal

Resolve the difference between ordered origin observations, reflected common-return
observations, and an arbitrary phase. The proposed universal horizon is `2N-3`
samples. Contribution 007 proves a sharp return-window classification but supplies
no upper bound at arbitrary phases. The conjecture is neither proved nor falsified.

## Established evidence

- 005: first `N-1` observations from the origin determine the entire nonconstant tail.
- 007: at explicit common returns, the complete window kernel is the initial kernel
  plus the reflection defect `H-Σc`; positive radii impose two tail moments.
- For all `N=n+4`, the final normalized triple `(1,-2,1)` produces exactly
  `2N-4` consecutive zeros around the constructed common return, with nonzero
  adjacent values and nonzero variance. This is fully formalized in
  `ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean`.
- First differences turn a translated zero block into shifted divisor-hit equations.
  No current argument proves those equations have full rank at every phase.
- Generic periodicity, complete-period covariance and the origin's triangular
  inverse do not close this gap. The translation closure may have a much larger
  dimension than the original coefficient space; do not conflate them.

## Counting boundary

The return-window kernel, exact lower-bound family and extremal rigidity count
together as contribution 007. A matching uniform upper bound or direct refinement
must not receive a second count for that same package. No credit is assigned here.

## Approach and corpus status

Use symbolic structure of shifted divisor incidence, or find an exact obstruction
and classify its strongest positive survivor. No numerical experiments, no external
research. Refresh the local corpus before new Lean source. Relevant partial deep
audits and all inspected candidate/source-argument counts are recorded on
`docs/drafts/pipeline/3-formalized/bvi-translated-prefix-observability-and-maximal-zero-runs-2026-10-18.md`.
There is no dependency-closed paper proof of this conjecture and no Lean module yet.

## Gates

- [ ] Complete refreshed corpus audit and choose a viable attack.
- [ ] Dependency-closed paper proof or exact obstruction with positive survivor.
- [ ] Formalize the exact surviving statement; named-source and axiom audits.

## No-go closure

The route is open, not retired. If falsified, record the killing mechanism and
extract a sharp corrected horizon, exact phase classification, or another nontrivial
positive invariant. Formalize a dependency-closed survivor before retirement.
