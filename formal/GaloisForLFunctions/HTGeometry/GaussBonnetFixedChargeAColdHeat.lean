import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdThermalSlopes
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdLatent

/-!
# Opposite cold behavior of the two actual heat capacities

The small-phase heat capacity vanishes linearly with temperature, with an
explicit positive coefficient. The large-phase heat capacity grows like
four times its leading entropy area, despite the same temperature tending
to zero. Every quantity uses the actual entropy and temperature derivatives.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAColdHeatCoefficient (w φ : ℝ) : ℝ :=
  4 * Real.pi ^ (2 : ℕ) * exp w ^ (3 : ℕ) * (1 + 2 * egbFixedChargeAFraction φ) ^ (2 : ℕ)

theorem egbFixedChargeAColdHeatCoefficient_pos (w φ : ℝ) : 0 < egbFixedChargeAColdHeatCoefficient w φ := by
  have hρ := (egbFixedChargeAFraction_bounds φ).1
  unfold egbFixedChargeAColdHeatCoefficient
  positivity

theorem egbFixedChargeAColdHeatCoefficient_response (w φ : ℝ) :
    egbFixedChargeAColdEntropySlope w φ / egbFixedChargeAColdRadialSlope w φ = egbFixedChargeAColdHeatCoefficient w φ := by
  unfold egbFixedChargeAColdEntropySlope egbFixedChargeAColdRadialSlope egbFixedChargeAColdHeatCoefficient
  field_simp <;> ring

theorem egbFixedChargeA_small_entropy_slope_formula (w φ τ l : ℝ) :
    deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeASmallRadius w φ τ) =
      2 * Real.pi * (egbFixedChargeASmallRadius w φ τ) + 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / (egbFixedChargeASmallRadius w φ τ) := by
  have hR : 0 < egbFixedChargeASmallRadius w φ τ := (egbFixedChargeA_radii_order w φ τ).1
  have h := (egbEntropyA_derivative (exp w * sin φ) l (log (egbFixedChargeASmallRadius w φ τ))).deriv
  rwa [exp_log hR] at h

theorem egbFixedChargeA_large_entropy_slope_formula (w φ τ l : ℝ) :
    deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeALargeRadius w φ τ) =
      2 * Real.pi * (egbFixedChargeALargeRadius w φ τ) + 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / (egbFixedChargeALargeRadius w φ τ) := by
  have hR : 0 < egbFixedChargeALargeRadius w φ τ := egbFixedChargeALargeRadius_pos w φ τ
  have h := (egbEntropyA_derivative (exp w * sin φ) l (log (egbFixedChargeALargeRadius w φ τ))).deriv
  rwa [exp_log hR] at h

theorem egbFixedChargeA_small_entropy_slope_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeASmallRadius w φ τ)) atTop
      (𝓝 (egbFixedChargeAColdEntropySlope w φ)) := by
  simp only [egbFixedChargeA_small_entropy_slope_formula]
  have hR := egbFixedChargeASmallRadius_cold_limit w φ
  have h : Tendsto (fun τ => 2 * Real.pi * egbFixedChargeASmallRadius w φ τ +
      4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / egbFixedChargeASmallRadius w φ τ) atTop
      (𝓝 (2 * Real.pi * exp w + 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / exp w)) :=
    (tendsto_const_nhds.mul hR).add (tendsto_const_nhds.div hR (exp_ne_zero w))
  have he : 2 * Real.pi * exp w + 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / exp w = egbFixedChargeAColdEntropySlope w φ := by
    unfold egbFixedChargeAColdEntropySlope
    rw [egbFixedChargeA_cold_coupling_scaling]
    field_simp <;> ring
  rwa [he] at h

theorem egbFixedChargeA_large_entropy_slope_normalized (w φ τ l : ℝ) :
    deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeALargeRadius w φ τ) / egbFixedChargeALargeRadius w φ τ =
      2 * Real.pi * (1 + 2 * egbFixedChargeACouplingWeight τ φ) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  rw [egbFixedChargeA_large_entropy_slope_formula, egbFixedChargeA_coupling_scaling]
  field_simp <;> ring

theorem egbFixedChargeA_large_entropy_slope_scaled_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeALargeRadius w φ τ) /
      egbFixedChargeALargeRadius w φ τ) atTop (𝓝 (2 * Real.pi)) := by
  simp only [egbFixedChargeA_large_entropy_slope_normalized]
  have h : Tendsto (fun τ => 2 * Real.pi * (1 + 2 * egbFixedChargeACouplingWeight τ φ)) atTop
      (𝓝 (2 * Real.pi * (1 + 2 * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul (egbFixedChargeACouplingWeight_cold_limit φ)))
  norm_num at h
  exact h

theorem egbFixedChargeA_small_heat_temperature_formula (w φ τ l : ℝ) :
    egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) /
      egbFixedChargeATemperature w φ τ =
    deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeASmallRadius w φ τ) /
      egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ) := by
  have hT := egbFixedChargeATemperature_pos w φ τ
  unfold egbHeatCapacityA
  rw [egbFixedChargeA_small_temperature, egbFixedChargeA_small_thermal_slope_formula]
  field_simp

theorem egbFixedChargeA_small_heat_temperature_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ =>
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) /
        egbFixedChargeATemperature w φ τ) atTop (𝓝 (egbFixedChargeAColdHeatCoefficient w φ)) := by
  simp only [egbFixedChargeA_small_heat_temperature_formula]
  have h := (egbFixedChargeA_small_entropy_slope_cold_limit w φ l).div
    (egbFixedChargeA_small_radial_slope_cold_limit w φ) (egbFixedChargeAColdRadialSlope_pos w φ).ne'
  rwa [egbFixedChargeAColdHeatCoefficient_response] at h

theorem egbFixedChargeA_small_heat_capacity_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeASmallRadius w φ τ)) atTop (𝓝 0) := by
  have h := (egbFixedChargeA_small_heat_temperature_cold_limit w φ l).mul (egbFixedChargeATemperature_cold_limit w φ)
  have he : (fun τ =>
      (egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) /
        egbFixedChargeATemperature w φ τ) * egbFixedChargeATemperature w φ τ) =
      (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ)) := by
    funext τ
    have hT := egbFixedChargeATemperature_pos w φ τ
    field_simp
  rw [he] at h
  simpa only [mul_zero] using h

theorem egbFixedChargeA_large_heat_capacity_area_formula (w φ τ l : ℝ) :
    egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
      (Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) =
    (egbFixedChargeATemperature w φ τ * egbFixedChargeALargeRadius w φ τ) *
      (deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeALargeRadius w φ τ) / egbFixedChargeALargeRadius w φ τ) /
        (Real.pi * (egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
          (egbFixedChargeALargeRadius w φ τ) * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ))) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  unfold egbHeatCapacityA
  rw [egbFixedChargeA_large_temperature, egbFixedChargeA_large_thermal_slope_formula]
  field_simp <;> ring

/-- The large phase has a universal heat-capacity-to-area coefficient of four. -/
theorem egbFixedChargeA_large_heat_capacity_area_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ =>
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
        (Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ))) atTop (𝓝 4) := by
  simp only [egbFixedChargeA_large_heat_capacity_area_formula]
  have h := ((egbFixedChargeATemperature_radius_cold_limit w φ).mul
    (egbFixedChargeA_large_entropy_slope_scaled_cold_limit w φ l)).div
      ((tendsto_const_nhds (x := Real.pi)).mul (egbFixedChargeA_large_radial_slope_scaled_cold_limit w φ)) (by positivity)
  have he : ((1 / Real.pi) * (2 * Real.pi)) / (Real.pi * (1 / (2 * Real.pi))) = (4 : ℝ) := by field_simp <;> ring
  rw [he] at h
  simpa only [Pi.div_def] using h

theorem egbFixedChargeA_large_heat_capacity_radius_square_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ =>
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
        egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) atTop (𝓝 (4 * Real.pi)) := by
  have h := (egbFixedChargeA_large_heat_capacity_area_cold_limit w φ l).mul (tendsto_const_nhds (x := Real.pi))
  have he : (fun τ =>
      (egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
        (Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ))) * Real.pi) =
      (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
        (egbFixedChargeALargeRadius w φ τ) / egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) := by
    funext τ
    field_simp
  rwa [he] at h

theorem egbFixedChargeA_large_heat_capacity_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeALargeRadius w φ τ)) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (show 0 < 4 * Real.pi by positivity)
    (egbFixedChargeA_large_heat_capacity_radius_square_cold_limit w φ l) (egbFixedChargeALargeRadius_square_cold_limit w φ)
  have he : (fun τ =>
      (egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
        egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) =
      (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp
  rwa [he] at h

end GaloisForLFunctions.HTGeometry
