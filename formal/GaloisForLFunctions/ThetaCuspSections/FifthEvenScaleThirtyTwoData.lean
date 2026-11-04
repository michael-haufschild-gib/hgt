import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightData

/-!
# A negative cross-load comparison at theta scale thirty-two

The last Gaussian coordinate detects a negative diagonal after subtracting
216 times the first-atom squared profile. A unit diagonal allowance remains
available for the complete-source error.
-/

noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ThirtyTwoCrossData
open EightCrossData
open scoped EightCrossData

/-- The last Gaussian coordinate is negative despite a unit diagonal allowance. -/
theorem upper_model_last_negative : polyModel 32 0 (-216*61^2) 1 4 4 < 0 := by
  norm_cross_model

end GaloisForLFunctions.ThetaCuspSections.ThirtyTwoCrossData
