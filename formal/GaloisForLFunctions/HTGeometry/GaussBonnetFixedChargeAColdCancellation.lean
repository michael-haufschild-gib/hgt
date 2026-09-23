import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdGibbs
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdThermalSlopes

/-!
# Cancellation of divergent enthalpy and thermal entropy in cold Gibbs energy

The large phase has M/R → 1 and TS/R → 1 while its Gibbs energy has the
finite extremal limit. Control of coupling times log R comes from the
finite small radius and the exact logarithmic kernel identity. Thus the
cancellation is established for the actual thermodynamic functions.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbFixedChargeA_large_log_radius_split (w φ τ : ℝ) :
    log (egbFixedChargeALargeRadius w φ τ) =
      log (egbFixedChargeASmallRadius w φ τ) - log (thermalRatio τ) := by
  unfold egbFixedChargeASmallRadius
  rw [log_mul (thermalRatio_pos τ).ne' (egbFixedChargeALargeRadius_pos w φ τ).ne']
  ring

theorem egbFixedChargeA_large_weighted_log_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeACouplingWeight τ φ * log (egbFixedChargeALargeRadius w φ τ)) atTop (𝓝 0) := by
  have he : (fun τ => egbFixedChargeACouplingWeight τ φ * log (egbFixedChargeALargeRadius w φ τ)) =
      (fun τ => egbFixedChargeACouplingWeight τ φ * log (egbFixedChargeASmallRadius w φ τ) -
        egbFixedChargeACouplingWeight τ φ * log (thermalRatio τ)) := by
    funext τ
    rw [egbFixedChargeA_large_log_radius_split]
    ring
  rw [he]
  have h := ((egbFixedChargeACouplingWeight_cold_limit φ).mul (egbFixedChargeA_small_log_radius_cold_limit w φ)).sub
    (egbFixedChargeA_log_product_cold_limit φ)
  simpa only [zero_mul, sub_zero] using h

theorem egbFixedChargeA_large_reference_log_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeACouplingWeight τ φ * (log (egbFixedChargeALargeRadius w φ τ) - l)) atTop (𝓝 0) := by
  have he : (fun τ => egbFixedChargeACouplingWeight τ φ * (log (egbFixedChargeALargeRadius w φ τ) - l)) =
      (fun τ => egbFixedChargeACouplingWeight τ φ * log (egbFixedChargeALargeRadius w φ τ) - egbFixedChargeACouplingWeight τ φ * l) := by
    funext τ
    ring
  rw [he]
  have h := (egbFixedChargeA_large_weighted_log_cold_limit w φ).sub
    ((egbFixedChargeACouplingWeight_cold_limit φ).mul (tendsto_const_nhds (x := l)))
  simpa only [zero_mul, sub_zero] using h

theorem egbFixedChargeA_large_entropy_area_formula (w φ τ l : ℝ) :
    egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
      (Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) =
        1 + 4 * (egbFixedChargeACouplingWeight τ φ * (log (egbFixedChargeALargeRadius w φ τ) - l)) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  unfold egbEntropyA
  rw [log_div hR.ne' (exp_ne_zero l), log_exp, egbFixedChargeA_coupling_scaling]
  field_simp <;> ring

theorem egbFixedChargeA_large_entropy_area_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
      (Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ))) atTop (𝓝 1) := by
  simp only [egbFixedChargeA_large_entropy_area_formula]
  have h : Tendsto (fun τ => 1 + 4 * (egbFixedChargeACouplingWeight τ φ * (log (egbFixedChargeALargeRadius w φ τ) - l)))
      atTop (𝓝 ((1 : ℝ) + 4 * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (egbFixedChargeA_large_reference_log_cold_limit w φ l))
  norm_num at h
  exact h

theorem egbFixedChargeA_large_entropy_radius_square_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
      egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) atTop (𝓝 Real.pi) := by
  have h := (egbFixedChargeA_large_entropy_area_cold_limit w φ l).mul (tendsto_const_nhds (x := Real.pi))
  have he : (fun τ => (egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
      (Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ))) * Real.pi) =
      (fun τ => egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) / egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) := by
    funext τ
    field_simp
  rw [he] at h
  simpa only [one_mul] using h

theorem egbFixedChargeA_large_entropy_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop Real.pi_pos (egbFixedChargeA_large_entropy_radius_square_cold_limit w φ l)
    (egbFixedChargeALargeRadius_square_cold_limit w φ)
  have he : (fun τ => (egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
      egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) =
      (fun τ => egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp
  rwa [he] at h

theorem egbFixedChargeA_large_mass_radius_formula (w φ τ : ℝ) :
    egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) /
      egbFixedChargeALargeRadius w φ τ = 1 / 2 + egbFixedChargeAWeight τ φ / 2 + egbFixedChargeAPressureWeight τ φ / 6 := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  unfold egbMass egbFixedChargeAPressure
  rw [egbFixedChargeA_effective_charge_scaling]
  field_simp <;> ring

theorem egbFixedChargeA_large_mass_radius_cold_limit (w φ : ℝ) :
    Tendsto (fun τ =>
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) /
        egbFixedChargeALargeRadius w φ τ) atTop (𝓝 1) := by
  simp only [egbFixedChargeA_large_mass_radius_formula]
  have h : Tendsto (fun τ => 1 / 2 + egbFixedChargeAWeight τ φ / 2 + egbFixedChargeAPressureWeight τ φ / 6)
      atTop (𝓝 ((1 : ℝ) / 2 + 0 / 2 + 3 / 6)) :=
    (tendsto_const_nhds.add ((egbFixedChargeAWeight_cold_limit φ).div tendsto_const_nhds (by norm_num))).add
      ((egbFixedChargeAPressureWeight_cold_limit φ).div tendsto_const_nhds (by norm_num))
  norm_num at h
  exact h

theorem egbFixedChargeA_large_mass_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeALargeRadius w φ τ)) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (show (0 : ℝ) < 1 by norm_num)
    (egbFixedChargeA_large_mass_radius_cold_limit w φ) (egbFixedChargeALargeRadius_cold_limit w φ)
  have he : (fun τ =>
      (egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) /
        egbFixedChargeALargeRadius w φ τ) * egbFixedChargeALargeRadius w φ τ) =
      (fun τ => egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp
  rwa [he] at h

theorem egbFixedChargeA_large_thermal_entropy_radius_formula (w φ τ l : ℝ) :
    egbFixedChargeATemperature w φ τ * egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) /
      egbFixedChargeALargeRadius w φ τ =
    (egbFixedChargeATemperature w φ τ * egbFixedChargeALargeRadius w φ τ) *
      (egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) / egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  field_simp <;> ring

theorem egbFixedChargeA_large_thermal_entropy_radius_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperature w φ τ *
      egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) / egbFixedChargeALargeRadius w φ τ)
        atTop (𝓝 1) := by
  simp only [egbFixedChargeA_large_thermal_entropy_radius_formula]
  have h := (egbFixedChargeATemperature_radius_cold_limit w φ).mul (egbFixedChargeA_large_entropy_radius_square_cold_limit w φ l)
  simpa only [one_div, inv_mul_cancel₀ Real.pi_ne_zero] using h

theorem egbFixedChargeA_large_thermal_entropy_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperature w φ τ *
      egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (show (0 : ℝ) < 1 by norm_num)
    (egbFixedChargeA_large_thermal_entropy_radius_cold_limit w φ l) (egbFixedChargeALargeRadius_cold_limit w φ)
  have he : (fun τ => (egbFixedChargeATemperature w φ τ *
      egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) / egbFixedChargeALargeRadius w φ τ) *
        egbFixedChargeALargeRadius w φ τ) = (fun τ => egbFixedChargeATemperature w φ τ *
          egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp
  rwa [he] at h

end GaloisForLFunctions.HTGeometry
