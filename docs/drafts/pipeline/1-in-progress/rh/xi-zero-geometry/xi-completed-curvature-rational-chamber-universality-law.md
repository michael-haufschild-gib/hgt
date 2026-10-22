# Xi completed-curvature rational-chamber universality law

- **ID:** xi-completed-curvature-rational-chamber-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of completed-Xi/filtered-prime curvature identity and
  upper-end rational chamber-gauge invariance
- **Statement:** Raw completed-Xi curvature, its corrected two-step translation defect, and
  filtered von Mangoldt curvature remain hypertranscendental after arbitrary independent rational
  upper-end gauge shifts.  The independently gauged defect and prime curvature differ by exactly
  the rational gauge difference.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `xiCompletedCurvatureRotatedUpperEnd_translation_defect`
- `xiCompletedCurvatureRotatedUpperEndCarrier_hypertranscendentalOver`
- `xiShiftTwoCorrectedCompletedCurvatureUpperEndCarrier_hypertranscendentalOver`
- `filteredVonMangoldtCompletedCurvatureUpperEndCarrier_hypertranscendentalOver`
- `hypertranscendentalOver_upperEnd_addRational_iff`

## Proof

`[PROVED HERE]` The completed curvature, corrected translation defect, and filtered prime
curvature are each hypertranscendental over the embedded rational upper-end coordinate field.
Adding any element of that base field preserves hypertranscendence.  The ungauged corrected defect
equals the filtered prime curvature exactly.  Subtracting independently gauged presentations
cancels their shared nonrational carrier and leaves precisely the embedded difference of the two
rational gauges.  No computation is used.

## Strict gain over corpus endpoints

The Xi theorem fixes one presentation and one exact equality.  The chamber theorem is generic and
has no completed-zeta carrier.  Their closure classifies the entire rational chamber of the actual
completed-Xi curvature bridge: all presentations retain hypertranscendence, and any two defect/prime
presentations differ by a completely explicit rational torsor coordinate.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiCompletedCurvatureRationalChamberUniversalityLaw`
- Main theorem:
  `xiCompletedCurvature_rationalChamberUniversality`
- Source:
  `formal/GaloisForLFunctions/RHTower/XiCompletedCurvatureRationalChamberUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/XiCompletedCurvatureRationalChamberUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for
completed Xi curvature, rational gauges, filtered von Mangoldt curvature, hypertranscendence, and
Xi logarithmic derivatives found adjacent work on Xi derivative positivity and logarithmic
derivative positivity, but no rational-chamber torsor statement and no filtered-prime curvature
identity of this form.  Closest inspected primary source:

- M. Coffey, *On a positivity property of the real part of logarithmic derivative of the Riemann
  ξ-function*, <https://arxiv.org/abs/2201.08599>.

## Log

- 2026-07-23 — Terminal cross-folder scan exposed the Xi-curvature/rational-chamber seam.
- 2026-07-23 — Dependency-closed proof completed from existing Lean endpoints.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
