import GaloisForLFunctions.ArithmeticIncidencePositivity.AWeilFloorSurvivesAnotherDilation
import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary

/-!
# The zeta onset strictly exceeds the first enlarged base

The second explicit dilation retains a positive Weil floor for every complex
window test. It therefore gives a strict improvement of the onset aperture.
-/

noncomputable section

open MeasureTheory Zeta23

namespace GaloisForLFunctions.WindowVisibilityLaw

open ArithmeticIncidencePositivity

/-- Every complex test at the second enlarged aperture has nonnegative Weil energy. -/
theorem windowPositiveAt_successorWeilFloorAperture :
    WindowPositiveAt zetaZeroConfig successorWeilFloorAperture := by
  intro f hf hfs
  have hfloor := zetaZeroConfig_re_W_ge_of_aperture_le_successorWeilFloorAperture hf hfs
  have hmass : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  linarith only [hfloor, hmass]

/-- The second explicit aperture is an unconditional lower bound for the zeta onset. -/
theorem successorWeilFloorAperture_le_onsetAperture_zeta :
    (successorWeilFloorAperture : EReal) ≤ onsetAperture zetaZeroConfig := by
  have ha : 0 ≤ successorWeilFloorAperture := by
    linarith only [enlargedWeilFloorAperture_bounds.1, successorWeilFloorAperture_bounds.1]
  exact le_onsetAperture_of_windowPositiveAt ha windowPositiveAt_successorWeilFloorAperture

/-- The original enlarged base is strictly below the actual onset. -/
theorem enlargedWeilFloorAperture_lt_onsetAperture_zeta :
    (enlargedWeilFloorAperture : EReal) < onsetAperture zetaZeroConfig :=
  (EReal.coe_lt_coe_iff.mpr successorWeilFloorAperture_bounds.1).trans_le
    successorWeilFloorAperture_le_onsetAperture_zeta

end GaloisForLFunctions.WindowVisibilityLaw

#print axioms GaloisForLFunctions.WindowVisibilityLaw.windowPositiveAt_successorWeilFloorAperture
#print axioms GaloisForLFunctions.WindowVisibilityLaw.enlargedWeilFloorAperture_lt_onsetAperture_zeta
