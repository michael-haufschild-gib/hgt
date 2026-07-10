# Canonical Perron--Mellin seam and source-gauge invariance

- **ID:** canonical-perron-mellin-seam-formal
- **Stage:** 3-formalized
- **Status:** `[PROVED, Lean]`
- **Date:** 2026-07-10
- **Paper theorem:** `docs/drafts/pipeline/2-fully-proven/new/canonical-perron-mellin-seam.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CanonicalPerronMellinSeam.lean`

## Strengthened defect interface

The parent module now also exposes:

- `HasCrossLineMellinDefectAt`
- `HasEventuallyCrossLineMellinDefect`
- `HasCrossLineMellinDefect.hasEventually`
- `coefficient_eq_sourceCharge_add_seamResidue_of_defectAt`
- `soninPerronMellinSeamResidue_tendsto_coefficient_of_eventuallyDefect`
- `soninPerronMellinSeamCoefficient_tendsto_coefficient_of_eventuallyDefect`

## Canonical formal surface

- `negativeLineLp`
- `canonicalCrossLineMellinDefect`
- `crossLineMellinDefectAt_unique`
- `hasCrossLineMellinDefectAt_canonical`
- `hasEventuallyCrossLineMellinDefect_canonical`
- `eventually_memLp_negativeLine_of_flankL2Energy`
- `soninPerronCanonicalSeamCoefficient_tendsto_coefficient_of_flankL2Energy`
- `soninPerronCanonicalSeamCoefficient_twoSource_sub_tendsto_zero`

The capstone consumes existing carrier flank energy and horizontal mass, constructs the seam defect
internally, and recovers the coefficient.  The two-source theorem proves asymptotic source-gauge
invariance.

## Verification

- [x] Target source elaborates directly.
- [x] Targeted Lake build passes (`8501/8501`); no umbrella build was run.
- [x] Principal theorem axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Generated API refreshed and `formal_tools.py lint --check-generated` passes.

## Remaining gate

`[OPEN CORE]` Construct an archimedean-completed Perron coordinate for
`xi=archFactor*riemannZeta` that retains completed negative-line decay while extracting an explicit
arithmetic coefficient plus computable Gamma/boundary charge.
