# Affine phase-curvature candidate fails its controls

Numerical arithmetic experiment, not an HB physical diagnostic or proof. Completed on pod B in 13.158 seconds including guard/cleanup, with 125.012 recorded worker seconds and at most 14 workers. All remote output checksums verified after download. No Lean builds.

The phase probe uses the gamma-free carrier values L(1/4+i*k*t/2) for k=1,3,5,7. It compares phase curvature at each of the first 64 zeta-zero ordinates with the adjacent midpoint, using matched local shifts. Three carriers share the same zeta-anchored sampling: zeta and the primitive real conductor-4 and conductor-5 Dirichlet L-functions. This tests conditioning on zeta ordinates; it does not sample the Dirichlet carriers' own zeros.

| Carrier | Mean 1:3:5 phase contrast R | Mean frequency-control contrast N |
|---|---:|---:|
| zeta | +0.274854756 | +0.161352169 |
| conductor 4 | -0.185584214 | +0.022095231 |
| conductor 5 | -0.214890613 | -0.047594316 |

The zeta R mean exceeds the frozen .05 threshold, but only five of eight consecutive eight-index block means share its sign (six required). It also fails the required factor-two dominance over its frequency control and both Dirichlet R means. The predeclared candidate therefore fails admission. Indices 65-128 and 257-320 were not computed for this statistic. No threshold was relaxed or alternative statistic substituted after inspection.

Validation: all 192 first-stage cells completed. Each carrier's largest absolute R-contrast cell was recomputed at 100 and 160 digits, retaining all six locations and four complex carrier values. Maximum contrast discrepancy from the 160-digit result was 4.53e-48 at 50 digits and 2.20e-98 at 100 digits. The smallest saved carrier magnitude was .31847, so phase normalization was not near a sampled zero. Twelve independently coded Euler-Maclaurin checks at 190 digits, each with an N/M refinement, have maximum scaled discrepancy 2.84e-189 and refinement difference 5.02e-190.

Interpretation: a positive low-cohort mean alone is inadequate evidence for a stable zeta-specific phase selector. Carrier and frequency controls are comparable, and the block signs vary. These finite data do not establish statistical independence, the absence of other phase structure, or a universal no-go for phase mechanisms. The block rule is a deterministic stability screen, not a population significance test.

Positive-salvage pass: the raw carrier contrasts and accurately resolved relative phases remain available, and the opposite carrier means are an exploratory observation. Choosing a new carrier subtraction after this failure would require a separately motivated question and fresh validation; it is not used to rescue the frozen candidate. Another enlarged scan of the same statistic is not justified. For the whole HB route, no source-forced phase relation has been supplied, and the full causal-action/corner assembly remains the larger missing step.

Reproduce with the exact recorded environment: python guard.py experiment.py; aggregate saved results with python analyze.py. PROTOCOL.md defines every statistic, threshold, sample and exclusion. Source search was cached and partial/source-only; source-provenance.json records inspected source and prior control checks. No physical theorem was transferred to the arithmetic controls.
