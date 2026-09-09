import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAStates
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeASmooth

/-!
# Actual equation-of-state tangents along fixed-charge coexistence

Differentiate the physical temperature with both pressure and radius
varying along the constructed path. The result separates the positive
radial thermal response from the exact pressure response.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbThermalPressureResponseA (a r : ℝ) : ℝ := 2 * r ^ 3 / (r ^ 2 + 2 * a ^ 2)

theorem egbTemperatureA_pressure_hasDerivAt (P Q a x : ℝ) :
    HasDerivAt (fun p => egbTemperatureA p Q a (exp x)) (egbThermalPressureResponseA a (exp x)) P := by
  have h := (((((hasDerivAt_id P).const_mul (8 * Real.pi)).mul_const (exp x ^ 4)).add_const
    (exp x ^ 2)).sub_const (Q ^ 2)).sub_const (a ^ 2)
  apply (h.div_const (4 * Real.pi * exp x * (exp x ^ 2 + 2 * a ^ 2))).congr_deriv
  unfold egbThermalPressureResponseA
  field_simp
  ring

theorem egbThermalPressureResponseA_pos (a x : ℝ) : 0 < egbThermalPressureResponseA a (exp x) := by
  unfold egbThermalPressureResponseA
  positivity

theorem egbFixedChargeA_large_equilibrium_derivative (w φ τ : ℝ) :
    deriv (egbFixedChargeATemperature w φ) τ =
      deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeALargeRadius w φ τ) * deriv (egbFixedChargeALargeRadius w φ) τ +
        egbThermalPressureResponseA (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) * deriv (egbFixedChargeAPressure w φ) τ := by
  have hRpos := egbFixedChargeALargeRadius_pos w φ τ
  have hr := ((egbFixedChargeALargeRadius_differentiable w φ) τ).hasDerivAt
  have hp := ((egbFixedChargeAPressure_differentiable w φ) τ).hasDerivAt
  have hN := (((((hp.const_mul (8 * Real.pi)).mul (hr.pow 4)).add (hr.pow 2)).sub_const
    ((exp w * cos φ) ^ 2)).sub_const ((exp w * sin φ) ^ 2))
  have hD := (hr.const_mul (4 * Real.pi)).mul ((hr.pow 2).add_const (2 * (exp w * sin φ) ^ 2))
  have h := hN.div hD (by change 4 * Real.pi * (egbFixedChargeALargeRadius w φ τ) * ((egbFixedChargeALargeRadius w φ τ) ^ 2 + 2 * (exp w * sin φ) ^ 2) ≠ 0; positivity)
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun u => (egbFixedChargeA_large_temperature w φ u).symm))
  have hRad := (egbTemperatureA_hasDerivAt (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (log (egbFixedChargeALargeRadius w φ τ))).deriv
  rw [exp_log hRpos] at hRad
  rw [h'.deriv, hRad]
  unfold egbTemperatureARadialSlope egbThermalPressureResponseA
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Nat.cast_ofNat]
  field_simp
  ring

theorem egbFixedChargeA_small_equilibrium_derivative (w φ τ : ℝ) :
    deriv (egbFixedChargeATemperature w φ) τ =
      deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeASmallRadius w φ τ) * deriv (egbFixedChargeASmallRadius w φ) τ +
        egbThermalPressureResponseA (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ) * deriv (egbFixedChargeAPressure w φ) τ := by
  have hRpos := (egbFixedChargeA_radii_order w φ τ).1
  have hr := ((egbFixedChargeASmallRadius_differentiable w φ) τ).hasDerivAt
  have hp := ((egbFixedChargeAPressure_differentiable w φ) τ).hasDerivAt
  have hN := (((((hp.const_mul (8 * Real.pi)).mul (hr.pow 4)).add (hr.pow 2)).sub_const
    ((exp w * cos φ) ^ 2)).sub_const ((exp w * sin φ) ^ 2))
  have hD := (hr.const_mul (4 * Real.pi)).mul ((hr.pow 2).add_const (2 * (exp w * sin φ) ^ 2))
  have h := hN.div hD (by change 4 * Real.pi * (egbFixedChargeASmallRadius w φ τ) * ((egbFixedChargeASmallRadius w φ τ) ^ 2 + 2 * (exp w * sin φ) ^ 2) ≠ 0; positivity)
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun u => (egbFixedChargeA_small_temperature w φ u).symm))
  have hRad := (egbTemperatureA_hasDerivAt (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (log (egbFixedChargeASmallRadius w φ τ))).deriv
  rw [exp_log hRpos] at hRad
  rw [h'.deriv, hRad]
  unfold egbTemperatureARadialSlope egbThermalPressureResponseA
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Nat.cast_ofNat]
  field_simp
  ring

theorem egbFixedChargeA_radius_derivative_relation (w φ τ : ℝ) :
    deriv (egbFixedChargeASmallRadius w φ) τ =
      (-exp τ * thermalRatio τ) * egbFixedChargeALargeRadius w φ τ +
        thermalRatio τ * deriv (egbFixedChargeALargeRadius w φ) τ :=
  ((thermalRatio_hasDerivAt τ).mul ((egbFixedChargeALargeRadius_differentiable w φ) τ).hasDerivAt).deriv

end GaloisForLFunctions.HTGeometry
