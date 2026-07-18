import GaloisForLFunctions.RHTower.XiUpperEndHypertranscendence

/-!
# Completed xi curvature from the filtered prime source

The corrected `+2` translation defect of the rotated completed logarithmic derivative is already
the filtered von Mangoldt carrier.  This module differentiates that exact value law.  Translation
commutes with the upper-end differential, so the corrected translation defect of the completed
curvature is exactly the derivative of the filtered prime carrier.

No new analytic estimate enters: the curvature identity is the derivative of
`xiLogDerivRotatedUpperEnd_translation_defect`, and both hypertranscendence statements are direct
instances of preservation under differentiation.
-/

namespace RHTower

open Complex
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiCurvatureUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiCurvatureUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiCurvatureUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- Actual upper-end carrier of the rotated completed curvature `(xi'/xi)'`. -/
noncomputable def xiCompletedCurvatureRotatedUpperEndCarrier : upperEndMeroField :=
  xiLogDerivRotatedUpperEndCarrier′

/-- Curvature of the rational correction in the completed `+2` shift law. -/
noncomputable def xiShiftTwoCompletedCurvatureCorrectionUpperEndCarrier : upperEndMeroField :=
  xiShiftTwoRationalCorrectionUpperEndCarrier′

/-- Curvature carrier of the filtered von Mangoldt source. -/
noncomputable def filteredVonMangoldtCompletedCurvatureUpperEndCarrier : upperEndMeroField :=
  filteredVonMangoldtUpperEndCarrier′

/-- **Exact corrected completed-curvature identity.**  The corrected `+2` translation defect of
the actual rotated completed curvature is exactly the curvature of the filtered prime carrier. -/
theorem xiCompletedCurvatureRotatedUpperEnd_translation_defect :
    upperEndTranslationMeroEquiv (2 * I) xiCompletedCurvatureRotatedUpperEndCarrier -
        xiCompletedCurvatureRotatedUpperEndCarrier -
        xiShiftTwoCompletedCurvatureCorrectionUpperEndCarrier =
      filteredVonMangoldtCompletedCurvatureUpperEndCarrier := by
  have hcurvature := congrArg Differential.deriv
    xiLogDerivRotatedUpperEnd_translation_defect
  rw [map_sub, map_sub, ← upperEndTranslationMeroEquiv_deriv] at hcurvature
  simpa only [xiCompletedCurvatureRotatedUpperEndCarrier,
    xiShiftTwoCompletedCurvatureCorrectionUpperEndCarrier,
    filteredVonMangoldtCompletedCurvatureUpperEndCarrier] using hcurvature

/-- The filtered von Mangoldt curvature carrier remains hypertranscendental over the genuine
upper-end rational coordinate field. -/
theorem filteredVonMangoldtCompletedCurvatureUpperEndCarrier_hypertranscendentalOver :
    HypertranscendentalOver upperEndRationalCoordinateField
      filteredVonMangoldtCompletedCurvatureUpperEndCarrier := by
  simpa only [filteredVonMangoldtCompletedCurvatureUpperEndCarrier] using
    hypertranscendentalOver_deriv
      filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver

/-- The exact corrected completed-curvature translation defect is unconditionally
hypertranscendental over the genuine upper-end rational coordinate field. -/
theorem xiShiftTwoCorrectedCompletedCurvatureUpperEndCarrier_hypertranscendentalOver :
    HypertranscendentalOver upperEndRationalCoordinateField
      (upperEndTranslationMeroEquiv (2 * I) xiCompletedCurvatureRotatedUpperEndCarrier -
        xiCompletedCurvatureRotatedUpperEndCarrier -
          xiShiftTwoCompletedCurvatureCorrectionUpperEndCarrier) := by
  rw [xiCompletedCurvatureRotatedUpperEnd_translation_defect]
  exact filteredVonMangoldtCompletedCurvatureUpperEndCarrier_hypertranscendentalOver

/-- **Unconditional completed-curvature capstone.**  The actual rotated completed curvature
`(xi'/xi)'` is hypertranscendental over the genuine upper-end rational coordinate field. -/
theorem xiCompletedCurvatureRotatedUpperEndCarrier_hypertranscendentalOver :
    HypertranscendentalOver upperEndRationalCoordinateField
      xiCompletedCurvatureRotatedUpperEndCarrier := by
  simpa only [xiCompletedCurvatureRotatedUpperEndCarrier] using
    hypertranscendentalOver_deriv
      xiLogDerivRotatedUpperEndCarrier_hypertranscendentalOver

end

end RHTower
