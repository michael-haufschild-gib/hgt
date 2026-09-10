import GaloisForLFunctions.HTGeometry.GomesFiniteFockExponentialCoordinate
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonLogPotential

/-!
# Exact formal logarithms of the rescaled exponential clock

The existing logarithmic differential identity from projective horizons gives
an explicit inverse coordinate for the actual Fock translation family.
All complex parameters, including zero, are retained.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Formal differentiation obeys the rescaling chain rule, including zero scale. -/
theorem gomesFormalSeries_derivative_rescale (z : ℂ) (F : PowerSeries ℂ) :
    PowerSeries.derivative ℂ (PowerSeries.rescale z F) =
      z • PowerSeries.rescale z (PowerSeries.derivative ℂ F) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, map_smul,
    smul_eq_mul, pow_succ]
  ring

/-- Every rescaled formal exponential has unit constant coefficient. -/
theorem gomesFormalSeries_rescale_exp_constantCoeff (z : ℂ) :
    PowerSeries.constantCoeff (PowerSeries.rescale z (PowerSeries.exp ℂ)) = 1 := by
  have h := gomesFiniteFockExponentialIncrement_constantCoeff z
  simpa only [map_sub, map_one, sub_eq_zero] using h

/-- The horizon logarithmic differential recovers the exact linear clock coordinate. -/
theorem gomesFormalSeries_logOf_rescale_exp (z : ℂ) :
    PowerSeries.logOf (PowerSeries.rescale z (PowerSeries.exp ℂ)) =
      z • (PowerSeries.X : PowerSeries ℂ) := by
  have h0 := gomesFormalSeries_rescale_exp_constantCoeff z
  apply PowerSeries.derivative.ext
  · rw [derivative_logOf h0, gomesFormalSeries_derivative_rescale,
      PowerSeries.derivative_exp, Derivation.map_smul, PowerSeries.derivative_X, mul_smul_comm,
      PowerSeries.inv_mul_cancel (h := by rw [h0]; exact one_ne_zero)]
  · rw [PowerSeries.constantCoeff_logOf h0]
    simp

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
