import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalResponse
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMonotonicity
import Mathlib.Topology.Algebra.Order.Field

/-!
# Divergence of both actual phase heat capacities at the critical endpoint

Each stable phase has a positive radial temperature derivative that tends
to zero, while T times the entropy derivative tends to a strictly positive
constant. Consequently the actual isobaric heat capacities of both phases
tend to positive infinity, for every fixed charge and coupling fraction.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeACriticalHeatNumerator (w φ : ℝ) : ℝ :=
  egbFixedChargeACriticalTemperature w φ * (2 * Real.pi * egbFixedChargeACriticalRadius w φ +
    4 * Real.pi * (exp w * sin φ) ^ 2 / egbFixedChargeACriticalRadius w φ)

theorem egbFixedChargeACriticalHeatNumerator_pos (w φ : ℝ) :
    0 < egbFixedChargeACriticalHeatNumerator w φ := by
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have hT := egbFixedChargeACriticalTemperature_pos w φ
  unfold egbFixedChargeACriticalHeatNumerator
  positivity

theorem egbFixedChargeA_small_thermal_slope_formula (w φ τ : ℝ) :
    deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeASmallRadius w φ τ) =
      egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ) := by
  have hR : 0 < egbFixedChargeASmallRadius w φ τ := (egbFixedChargeA_radii_order w φ τ).1
  have h := (egbTemperatureA_hasDerivAt (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (log (egbFixedChargeASmallRadius w φ τ))).deriv
  rw [exp_log hR] at h
  exact h

theorem egbFixedChargeA_small_radial_slope_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) atBot (𝓝 0) := by
  have hP := egbFixedChargeAPressure_critical_limit w φ
  have hR := egbFixedChargeASmallRadius_critical_limit w φ
  have hRc := egbFixedChargeACriticalRadius_pos w φ
  have h : Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) atBot (𝓝 (egbTemperatureARadialSlope (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeACriticalRadius w φ))) :=
    ((((((tendsto_const_nhds.mul hP).mul (hR.pow 6)).add
      (((tendsto_const_nhds.mul hP).mul tendsto_const_nhds).mul (hR.pow 4))).sub
        (hR.pow 4)).add (tendsto_const_nhds.mul (hR.pow 2))).add tendsto_const_nhds).div
          ((tendsto_const_nhds.mul (hR.pow 2)).mul (((hR.pow 2).add tendsto_const_nhds).pow 2))
            (by change 4 * Real.pi * (egbFixedChargeACriticalRadius w φ) ^ 2 * ((egbFixedChargeACriticalRadius w φ) ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2 ≠ 0; positivity)
  rwa [egbFixedChargeACritical_radial_slope_zero] at h

theorem egbFixedChargeA_small_actual_slope_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeASmallRadius w φ τ)) atBot (𝓝 0) := by
  simp only [egbFixedChargeA_small_thermal_slope_formula]
  exact egbFixedChargeA_small_radial_slope_critical_limit w φ

theorem egbFixedChargeA_small_heat_capacity_formula (w φ τ l : ℝ) :
    egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) =
      egbFixedChargeATemperature w φ τ * (2 * Real.pi * (egbFixedChargeASmallRadius w φ τ) + 4 * Real.pi * (exp w * sin φ) ^ 2 / (egbFixedChargeASmallRadius w φ τ)) /
        (egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) := by
  have hR : 0 < egbFixedChargeASmallRadius w φ τ := (egbFixedChargeA_radii_order w φ τ).1
  have h := egbHeatCapacityA_formula (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (log (egbFixedChargeASmallRadius w φ τ))
  rw [exp_log hR, egbFixedChargeA_small_temperature] at h
  exact h

theorem egbFixedChargeA_small_heat_numerator_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperature w φ τ *
      (2 * Real.pi * (egbFixedChargeASmallRadius w φ τ) + 4 * Real.pi * (exp w * sin φ) ^ 2 / (egbFixedChargeASmallRadius w φ τ)))
        atBot (𝓝 (egbFixedChargeACriticalHeatNumerator w φ)) :=
  (egbFixedChargeATemperature_critical_limit w φ).mul
    ((tendsto_const_nhds.mul (egbFixedChargeASmallRadius_critical_limit w φ)).add
      (tendsto_const_nhds.div (egbFixedChargeASmallRadius_critical_limit w φ) (egbFixedChargeACriticalRadius_pos w φ).ne'))

/-- Divergence of the genuine heat capacity, not merely a zero in a formal denominator. -/
theorem egbFixedChargeA_small_heat_capacity_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ)) atBot atTop := by
  have hs : Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) atBot (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨egbFixedChargeA_small_radial_slope_critical_limit w φ, Filter.Eventually.of_forall ?_⟩
    intro τ
    change 0 < egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)
    rw [← egbFixedChargeA_small_thermal_slope_formula]
    exact egbFixedChargeA_small_thermal_slope_pos w φ τ
  have h := Filter.Tendsto.pos_mul_atTop (egbFixedChargeACriticalHeatNumerator_pos w φ)
    (egbFixedChargeA_small_heat_numerator_critical_limit w φ) (tendsto_inv_nhdsGT_zero.comp hs)
  simpa only [egbFixedChargeA_small_heat_capacity_formula, Function.comp_def, div_eq_mul_inv] using h

theorem egbFixedChargeA_large_thermal_slope_formula (w φ τ : ℝ) :
    deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeALargeRadius w φ τ) =
      egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) := by
  have hR : 0 < egbFixedChargeALargeRadius w φ τ := egbFixedChargeALargeRadius_pos w φ τ
  have h := (egbTemperatureA_hasDerivAt (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (log (egbFixedChargeALargeRadius w φ τ))).deriv
  rw [exp_log hR] at h
  exact h

theorem egbFixedChargeA_large_radial_slope_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)) atBot (𝓝 0) := by
  have hP := egbFixedChargeAPressure_critical_limit w φ
  have hR := egbFixedChargeALargeRadius_critical_limit w φ
  have hRc := egbFixedChargeACriticalRadius_pos w φ
  have h : Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)) atBot (𝓝 (egbTemperatureARadialSlope (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeACriticalRadius w φ))) :=
    ((((((tendsto_const_nhds.mul hP).mul (hR.pow 6)).add
      (((tendsto_const_nhds.mul hP).mul tendsto_const_nhds).mul (hR.pow 4))).sub
        (hR.pow 4)).add (tendsto_const_nhds.mul (hR.pow 2))).add tendsto_const_nhds).div
          ((tendsto_const_nhds.mul (hR.pow 2)).mul (((hR.pow 2).add tendsto_const_nhds).pow 2))
            (by change 4 * Real.pi * (egbFixedChargeACriticalRadius w φ) ^ 2 * ((egbFixedChargeACriticalRadius w φ) ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2 ≠ 0; positivity)
  rwa [egbFixedChargeACritical_radial_slope_zero] at h

theorem egbFixedChargeA_large_actual_slope_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeALargeRadius w φ τ)) atBot (𝓝 0) := by
  simp only [egbFixedChargeA_large_thermal_slope_formula]
  exact egbFixedChargeA_large_radial_slope_critical_limit w φ

theorem egbFixedChargeA_large_heat_capacity_formula (w φ τ l : ℝ) :
    egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) =
      egbFixedChargeATemperature w φ τ * (2 * Real.pi * (egbFixedChargeALargeRadius w φ τ) + 4 * Real.pi * (exp w * sin φ) ^ 2 / (egbFixedChargeALargeRadius w φ τ)) /
        (egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)) := by
  have hR : 0 < egbFixedChargeALargeRadius w φ τ := egbFixedChargeALargeRadius_pos w φ τ
  have h := egbHeatCapacityA_formula (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (log (egbFixedChargeALargeRadius w φ τ))
  rw [exp_log hR, egbFixedChargeA_large_temperature] at h
  exact h

theorem egbFixedChargeA_large_heat_numerator_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperature w φ τ *
      (2 * Real.pi * (egbFixedChargeALargeRadius w φ τ) + 4 * Real.pi * (exp w * sin φ) ^ 2 / (egbFixedChargeALargeRadius w φ τ)))
        atBot (𝓝 (egbFixedChargeACriticalHeatNumerator w φ)) :=
  (egbFixedChargeATemperature_critical_limit w φ).mul
    ((tendsto_const_nhds.mul (egbFixedChargeALargeRadius_critical_limit w φ)).add
      (tendsto_const_nhds.div (egbFixedChargeALargeRadius_critical_limit w φ) (egbFixedChargeACriticalRadius_pos w φ).ne'))

/-- Divergence of the genuine heat capacity, not merely a zero in a formal denominator. -/
theorem egbFixedChargeA_large_heat_capacity_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) atBot atTop := by
  have hs : Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)) atBot (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨egbFixedChargeA_large_radial_slope_critical_limit w φ, Filter.Eventually.of_forall ?_⟩
    intro τ
    change 0 < egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)
    rw [← egbFixedChargeA_large_thermal_slope_formula]
    exact egbFixedChargeA_large_thermal_slope_pos w φ τ
  have h := Filter.Tendsto.pos_mul_atTop (egbFixedChargeACriticalHeatNumerator_pos w φ)
    (egbFixedChargeA_large_heat_numerator_critical_limit w φ) (tendsto_inv_nhdsGT_zero.comp hs)
  simpa only [egbFixedChargeA_large_heat_capacity_formula, Function.comp_def, div_eq_mul_inv] using h

end GaloisForLFunctions.HTGeometry
