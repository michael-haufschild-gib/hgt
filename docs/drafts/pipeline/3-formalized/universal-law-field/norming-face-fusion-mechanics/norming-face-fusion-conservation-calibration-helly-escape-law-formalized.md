# Norming-face fusion conservation, calibration, Helly witness, and escape law — formalized

- **ID:** `ulf-nffm-fusion-calibration-helly-escape-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper parent:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/norming-face-fusion-mechanics/norming-face-fusion-conservation-calibration-helly-escape-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.NormingFaceFusion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UNCONDITIONAL] [NO SORRY] [NOT RH]`

## Certified declarations

| Paper law | Lean declaration |
|---|---|
| contractive calibration residual is nonnegative | `calibrationResidual_nonneg` |
| exact variational attainment | `exists_calibrator_attains_fusionDefect` |
| variational lower bound for every calibrator | `fusionDefect_le_calibrationResidualSum` |
| nonnegative fusion defect | `fusionDefect_nonneg` |
| perfect fusion iff common calibrator | `fusionDefect_eq_zero_iff_exists_commonCalibrator` |
| norming faces are nonempty and convex | `normingFace_nonempty`, `normingFace_convex` |
| continuous dual has source dimension | `strongDual_finrank_eq` |
| finite Helly common calibration | `exists_commonCalibrator_of_small` |
| bounded witness arity | `fusionDefect_eq_zero_of_smallPackets_primal` |
| minimal-defect dimension bound | `minimallyDefective_pred_card_le_finrank` |
| exact observer exchange | `fusionDefect_observer_exchange` |
| exact refinement conservation | `fusionDefect_binary_refinement` |

## Scope

Lean certifies the coordinate-free finite mechanism. The complex phase, finite-port incidence, and
trace-norm spectral gauges are paper-level specializations. The cofinal consequence is certified
as the finite lower bound `card(packet)-1 <= finrank(V)`; passage to a particular infinite source
requires a separately constructed compatible packet family.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/NormingFaceFusion.lean`: pass.
- `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`: pass, 11,614 jobs.
- `scripts/formal_tools.py lint --check-generated`: pass.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
