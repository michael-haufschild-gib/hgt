import GaloisForLFunctions.HTGeometry.HyperbolicSineScaleMonotonicity
import GaloisForLFunctions.HTGeometry.ThermalAmplificationFluctuations

/-!
# Strict decrease of thermal radiation Fisher information

The scale comparison in arXiv:2609.20367, Corollary 6.39, applies to the
actual infinite occupation distribution: its Fisher information is the
paper's response `x² exp(-x)/(1-exp(-x))²` at `x = exp tau`.
-/

namespace GaloisForLFunctions.HTGeometry.CPV

/-- The infinite Fisher series equals the reciprocal hyperbolic response. -/
theorem radiationNumberFisher_sinh (tau : ℝ) :
    radiationNumberFisher tau =
      ((Real.exp tau / 2) / Real.sinh (Real.exp tau / 2)) ^ 2 := by
  rw [radiationNumberFisher_formula, radiationNumberVariance_formula, thermalRatio,
    _root_.HTGeometry.bose_fluctuation_eq_sinh]
  ring

/-- Increasing logarithmic inverse thermal scale strictly decreases the
information carried by the full occupation distribution. -/
theorem radiationNumberFisher_strictAnti : StrictAnti radiationNumberFisher := by
  intro x y hxy
  rw [radiationNumberFisher_sinh, radiationNumberFisher_sinh]
  apply _root_.HTGeometry.strictAntiOn_self_div_sinh_sq
  · change 0 < Real.exp x / 2
    positivity
  · change 0 < Real.exp y / 2
    positivity
  · exact div_lt_div_of_pos_right (Real.exp_lt_exp.mpr hxy) (by positivity)

/-- Every positive logarithmic scale increment produces strict information loss. -/
theorem radiationNumberFisher_scale_loss (tau step : ℝ) :
    radiationNumberFisher (tau + Real.exp step) < radiationNumberFisher tau :=
  radiationNumberFisher_strictAnti (by linarith [Real.exp_pos step])

end GaloisForLFunctions.HTGeometry.CPV
