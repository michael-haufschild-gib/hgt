import GaloisForLFunctions.HTGeometry.ChamberFamilyGaugeInvariance
import GaloisForLFunctions.RHTower.XiShiftPrimeCompletedCurvature

/-!
# Rational-chamber universality of completed Xi curvature

The corrected two-step translation defect of completed Xi curvature equals the filtered von
Mangoldt curvature.  Rational upper-end gauge shifts preserve hypertranscendence, so every
independently gauged presentation remains hypertranscendental and the two sides differ by exactly
their rational gauge displacement.
-/

namespace RHTower

open Complex
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

local instance xiCurvatureChamberDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiCurvatureChamberComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiCurvatureChamberDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiCurvatureChamberCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiCurvatureChamberDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    upperEndRationalCoordinateField
    upperEndRationalCoordinateField_derivationClosed x⟩

/-- **Xi completed-curvature rational-chamber universality law.**  Arbitrary rational upper-end
gauges preserve all three hypertranscendental carriers, while independently gauged defect and
prime presentations differ by exactly their rational gauge difference. -/
theorem xiCompletedCurvature_rationalChamberUniversality
    (bXi bDefect bPrime : upperEndRationalCoordinateField) :
    HypertranscendentalOver upperEndRationalCoordinateField
        (xiCompletedCurvatureRotatedUpperEndCarrier +
          (bXi : upperEndMeroField)) ∧
    HypertranscendentalOver upperEndRationalCoordinateField
        (upperEndTranslationMeroEquiv (2 * I)
              xiCompletedCurvatureRotatedUpperEndCarrier -
            xiCompletedCurvatureRotatedUpperEndCarrier -
            xiShiftTwoCompletedCurvatureCorrectionUpperEndCarrier +
          (bDefect : upperEndMeroField)) ∧
    HypertranscendentalOver upperEndRationalCoordinateField
        (filteredVonMangoldtCompletedCurvatureUpperEndCarrier +
          (bPrime : upperEndMeroField)) ∧
    ((upperEndTranslationMeroEquiv (2 * I)
              xiCompletedCurvatureRotatedUpperEndCarrier -
            xiCompletedCurvatureRotatedUpperEndCarrier -
            xiShiftTwoCompletedCurvatureCorrectionUpperEndCarrier +
          (bDefect : upperEndMeroField)) -
        (filteredVonMangoldtCompletedCurvatureUpperEndCarrier +
          (bPrime : upperEndMeroField)) =
      ((bDefect - bPrime : upperEndRationalCoordinateField) : upperEndMeroField)) := by
  constructor
  · exact
      (hypertranscendentalOver_upperEnd_addRational_iff
        xiCompletedCurvatureRotatedUpperEndCarrier bXi).2
        xiCompletedCurvatureRotatedUpperEndCarrier_hypertranscendentalOver
  constructor
  · exact
      (hypertranscendentalOver_upperEnd_addRational_iff
        (upperEndTranslationMeroEquiv (2 * I)
            xiCompletedCurvatureRotatedUpperEndCarrier -
          xiCompletedCurvatureRotatedUpperEndCarrier -
          xiShiftTwoCompletedCurvatureCorrectionUpperEndCarrier)
        bDefect).2
        xiShiftTwoCorrectedCompletedCurvatureUpperEndCarrier_hypertranscendentalOver
  constructor
  · exact
      (hypertranscendentalOver_upperEnd_addRational_iff
        filteredVonMangoldtCompletedCurvatureUpperEndCarrier bPrime).2
        filteredVonMangoldtCompletedCurvatureUpperEndCarrier_hypertranscendentalOver
  · rw [xiCompletedCurvatureRotatedUpperEnd_translation_defect]
    rw [show
      ((bDefect - bPrime : upperEndRationalCoordinateField) : upperEndMeroField) =
        (bDefect : upperEndMeroField) - (bPrime : upperEndMeroField) by rfl]
    ring

end

end RHTower
