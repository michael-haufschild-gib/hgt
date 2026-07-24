# Von Mangoldt Dirac–Krein reader/boundary flux-balance universality law

- **ID:** LAW453
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus theorem-posting closure
- **Statement:** For consecutive finite von Mangoldt Dirac–Krein sections with one fixed source marginal, cyclic-reader opening flux is exactly cancelled by the newly exposed weighted-density boundary flux; positive normalization and diagonal force strict reader growth, a negative boundary coefficient, and a Krein negative direction.

## Goal

Unify three separately formalized finite-section phenomena—cyclic-reader growth, weighted marginal
boundary anomaly, and Dirac–Krein indefiniteness—through their literal principal-relative moment
carrier.

## Gates

- [x] 0 → 1  in-progress: identical opening moment and exact Dirac–Krein realization identified
- [x] 1 → 2  fully-proven: dependency-closed elimination proof below
- [x] 2 → 3  formalized: Lean theorem
  `finiteVonMangoldtDiracKrein_readerBoundaryFluxObstructionUniversality`; exact-file check green
- [ ] 3 → 4  publication-ready: standalone paper pending

## Approach

At the opening from jet size `N+1` to `N+2`, the cyclic-reader law says

`reader increment = corner normalization · ρ_M(2(N+1)+2)`.

For any density realization preserving one source marginal across the same two sections, the
weighted marginal law says

`new diagonal · ρ_M(2(N+1)+2) + symmetric boundary flux = 0`.

Multiply the second identity by the reader corner normalization and substitute the first. This
eliminates the relative moment and yields exact reader/boundary flux balance. The finite
Dirac–Krein edge theorem identifies both jet sections with the principal-relative matrices used in
those two laws.

If `M>0`, corner normalization and the new diagonal are positive, the existing strict-opening law
makes the reader increment positive and the boundary-anomaly theorem forces at least one negative
symmetric boundary coefficient. The Dirac–Krein inertia theorem simultaneously gives a negative
direction for the same nonempty source aperture.

## No-go closure

Not applicable: positive survivor.

## Log

- 2026-07-23 — generated from `VonMangoldtCyclicReaderFluxNoGo`,
  `VonMangoldtWeightedMarginalBoundaryAnomaly`,
  `VonMangoldtSuccessorDiracKreinEdge`, and
  `VonMangoldtDiracKreinInertiaMarginalUniversalityLaw`
- 2026-07-23 — corpus research found all component laws but no theorem eliminating the shared
  opening moment into reader/boundary conservation
- 2026-07-23 — exact Lean check passed; wired into `GaloisForLFunctions.RHTower`
- 2026-07-23 — post-proof arXiv mechanism search found general Krein moment problems, Dirac
  boundary formulas, and Hankel spectra, but no von-Mangoldt finite-section
  cyclic-reader/boundary-flux conservation law
