import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHeat

/-!
# Actual radial thermal responses at the cold endpoint

The small phase reaches an extremal state with zero temperature but a
strictly positive radial temperature derivative. The large phase has a
universal inverse-square thermal-slope scale. All limits concern the
actual derivatives of the paper's temperature function.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAColdRadialSlope (w φ : ℝ) : ℝ :=
  1 / (2 * Real.pi * exp w ^ 2 * (1 + 2 * egbFixedChargeAFraction φ))
def egbFixedChargeAColdEntropySlope (w φ : ℝ) : ℝ :=
  2 * Real.pi * exp w * (1 + 2 * egbFixedChargeAFraction φ)

theorem egbFixedChargeA_effective_charge_scaling (w φ τ : ℝ) :
    (exp w * cos φ) ^ 2 + (exp w * sin φ) ^ 2 =
      egbFixedChargeALargeRadius w φ τ ^ 2 * egbFixedChargeAWeight τ φ := by
  rw [egbFixedChargeA_conserved_scale, egbFixedChargeA_effective_scale]

theorem egbFixedChargeA_cold_coupling_scaling (w φ : ℝ) :
    (exp w * sin φ) ^ 2 = exp w ^ 2 * egbFixedChargeAFraction φ := by
  unfold egbFixedChargeAFraction
  ring

theorem egbFixedChargeAColdRadialSlope_pos (w φ : ℝ) : 0 < egbFixedChargeAColdRadialSlope w φ := by
  have hρ := (egbFixedChargeAFraction_bounds φ).1
  unfold egbFixedChargeAColdRadialSlope
  positivity

theorem egbFixedChargeAColdEntropySlope_pos (w φ : ℝ) : 0 < egbFixedChargeAColdEntropySlope w φ := by
  have hρ := (egbFixedChargeAFraction_bounds φ).1
  unfold egbFixedChargeAColdEntropySlope
  positivity

theorem egbFixedChargeA_extremal_temperature (w φ : ℝ) :
    egbTemperatureA 0 (exp w * cos φ) (exp w * sin φ) (exp w) = 0 := by
  have h : exp w ^ 2 - (exp w * cos φ) ^ 2 - (exp w * sin φ) ^ 2 = 0 := by
    nlinarith [egbFixedChargeA_conserved_scale w φ]
  simp only [egbTemperatureA, mul_zero, zero_mul, zero_add, h, zero_div]

theorem egbFixedChargeA_extremal_radial_slope (w φ : ℝ) :
    egbTemperatureARadialSlope 0 (exp w * cos φ) (exp w * sin φ) (exp w) = egbFixedChargeAColdRadialSlope w φ := by
  have hρ := (egbFixedChargeAFraction_bounds φ).1
  unfold egbTemperatureARadialSlope egbFixedChargeAColdRadialSlope
  rw [egbFixedChargeA_conserved_scale, egbFixedChargeA_cold_coupling_scaling]
  field_simp
  ring

theorem egbFixedChargeA_extremal_temperature_derivative (w φ : ℝ) :
    deriv (egbTemperatureA 0 (exp w * cos φ) (exp w * sin φ)) (exp w) = egbFixedChargeAColdRadialSlope w φ := by
  rw [(egbTemperatureA_hasDerivAt 0 (exp w * cos φ) (exp w * sin φ) w).deriv,
    egbFixedChargeA_extremal_radial_slope]

theorem egbFixedChargeA_small_radial_slope_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ)
      (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) atTop
        (𝓝 (egbFixedChargeAColdRadialSlope w φ)) := by
  have hP := egbFixedChargeAPressure_cold_limit w φ
  have hR := egbFixedChargeASmallRadius_cold_limit w φ
  have h : Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ)
      (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) atTop
        (𝓝 (egbTemperatureARadialSlope 0 (exp w * cos φ) (exp w * sin φ) (exp w))) :=
    ((((((tendsto_const_nhds.mul hP).mul (hR.pow 6)).add
      (((tendsto_const_nhds.mul hP).mul tendsto_const_nhds).mul (hR.pow 4))).sub
        (hR.pow 4)).add (tendsto_const_nhds.mul (hR.pow 2))).add tendsto_const_nhds).div
          ((tendsto_const_nhds.mul (hR.pow 2)).mul (((hR.pow 2).add tendsto_const_nhds).pow 2))
            (by change 4 * Real.pi * exp w ^ 2 * (exp w ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2 ≠ 0; positivity)
  rwa [egbFixedChargeA_extremal_radial_slope] at h

theorem egbFixedChargeA_small_actual_slope_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ))
      (egbFixedChargeASmallRadius w φ τ)) atTop (𝓝 (egbFixedChargeAColdRadialSlope w φ)) := by
  simp only [egbFixedChargeA_small_thermal_slope_formula]
  exact egbFixedChargeA_small_radial_slope_cold_limit w φ

theorem egbFixedChargeA_large_radial_slope_normalized (w φ τ : ℝ) :
    egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeALargeRadius w φ τ) * egbFixedChargeALargeRadius w φ τ ^ 2 =
    (egbFixedChargeAPressureWeight τ φ * (1 + 6 * egbFixedChargeACouplingWeight τ φ) - 1 +
      2 * egbFixedChargeACouplingWeight τ φ + 3 * egbFixedChargeAWeight τ φ +
        2 * egbFixedChargeACouplingWeight τ φ * egbFixedChargeAWeight τ φ) /
          (4 * Real.pi * (1 + 2 * egbFixedChargeACouplingWeight τ φ) ^ 2) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  unfold egbTemperatureARadialSlope egbFixedChargeAPressure
  rw [egbFixedChargeA_effective_charge_scaling, egbFixedChargeA_coupling_scaling]
  field_simp
  ring

theorem egbFixedChargeA_large_radial_slope_scaled_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeALargeRadius w φ τ) * egbFixedChargeALargeRadius w φ τ ^ 2) atTop (𝓝 (1 / (2 * Real.pi))) := by
  simp only [egbFixedChargeA_large_radial_slope_normalized]
  have hp := egbFixedChargeAPressureWeight_cold_limit φ
  have hb := egbFixedChargeACouplingWeight_cold_limit φ
  have hs := egbFixedChargeAWeight_cold_limit φ
  have h : Tendsto (fun τ =>
      (egbFixedChargeAPressureWeight τ φ * (1 + 6 * egbFixedChargeACouplingWeight τ φ) - 1 +
        2 * egbFixedChargeACouplingWeight τ φ + 3 * egbFixedChargeAWeight τ φ +
          2 * egbFixedChargeACouplingWeight τ φ * egbFixedChargeAWeight τ φ) /
            (4 * Real.pi * (1 + 2 * egbFixedChargeACouplingWeight τ φ) ^ 2)) atTop
      (𝓝 (((3 : ℝ) * (1 + 6 * 0) - 1 + 2 * 0 + 3 * 0 + 2 * 0 * 0) /
        (4 * Real.pi * (1 + 2 * 0) ^ 2))) :=
    (((((hp.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hb))).sub tendsto_const_nhds).add
      (tendsto_const_nhds.mul hb)).add (tendsto_const_nhds.mul hs)).add
        ((tendsto_const_nhds.mul hb).mul hs)).div
          (tendsto_const_nhds.mul ((tendsto_const_nhds.add (tendsto_const_nhds.mul hb)).pow 2)) (by positivity)
  have he : ((3 : ℝ) * (1 + 6 * 0) - 1 + 2 * 0 + 3 * 0 + 2 * 0 * 0) /
      (4 * Real.pi * (1 + 2 * 0) ^ 2) = 1 / (2 * Real.pi) := by field_simp <;> ring
  rwa [he] at h

theorem egbFixedChargeA_large_actual_slope_scaled_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ))
      (egbFixedChargeALargeRadius w φ τ) * egbFixedChargeALargeRadius w φ τ ^ 2) atTop (𝓝 (1 / (2 * Real.pi))) := by
  simp only [egbFixedChargeA_large_thermal_slope_formula]
  exact egbFixedChargeA_large_radial_slope_scaled_cold_limit w φ

end GaloisForLFunctions.HTGeometry
