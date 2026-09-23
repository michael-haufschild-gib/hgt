import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalJumps
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalResponse

/-!
# Leading critical phase-gap coefficients and a universal enthalpy ratio

Normalize the actual phase discontinuities by one minus the radius
ratio. Their limits are finite and explicit. The latent heat per radius
separation tends to 2/3 for every fixed electric charge and coupling
fraction, matching the actual critical mass derivative.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeARadiusGap (w φ τ : ℝ) : ℝ :=
  egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ

theorem egbFixedChargeARadiusGap_pos (w φ τ : ℝ) : 0 < egbFixedChargeARadiusGap w φ τ :=
  sub_pos.mpr (egbFixedChargeA_radii_order w φ τ).2

theorem egbFixedChargeARadiusGap_formula (w φ τ : ℝ) :
    egbFixedChargeARadiusGap w φ τ = egbFixedChargeALargeRadius w φ τ * (1 - thermalRatio τ) := by
  unfold egbFixedChargeARadiusGap egbFixedChargeASmallRadius
  ring

theorem egbFixedChargeARadiusGap_normalized (w φ τ : ℝ) :
    egbFixedChargeARadiusGap w φ τ / (1 - thermalRatio τ) = egbFixedChargeALargeRadius w φ τ := by
  have hz := sub_pos.mpr (thermalRatio_lt_one τ)
  rw [egbFixedChargeARadiusGap_formula]
  field_simp

theorem egbFixedChargeARadiusGap_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeARadiusGap w φ) atBot (𝓝 0) := by
  change Tendsto (fun τ => egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ) atBot (𝓝 0)
  simpa only [sub_self] using (egbFixedChargeALargeRadius_critical_limit w φ).sub
    (egbFixedChargeASmallRadius_critical_limit w φ)

theorem egbFixedChargeARadiusGap_scaled_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeARadiusGap w φ τ / (1 - thermalRatio τ)) atBot
      (𝓝 (egbFixedChargeACriticalRadius w φ)) := by
  simp only [egbFixedChargeARadiusGap_normalized]
  exact egbFixedChargeALargeRadius_critical_limit w φ

theorem egbFixedChargeAEntropyJump_scaled_formula (w φ τ : ℝ) :
    egbFixedChargeAEntropyJump w φ τ / (1 - thermalRatio τ) =
      Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ) *
        (1 + thermalRatio τ + 4 * egbFixedChargeACouplingWeight τ φ * (log (thermalRatio τ) / (thermalRatio τ - 1))) := by
  have hz := sub_pos.mpr (thermalRatio_lt_one τ)
  have hn : thermalRatio τ - 1 ≠ 0 := by linarith
  rw [egbFixedChargeAEntropyJump_formula]
  field_simp
  ring

theorem egbFixedChargeAVolumeJump_scaled_formula (w φ τ : ℝ) :
    egbFixedChargeAVolumeJump w φ τ / (1 - thermalRatio τ) =
      4 * Real.pi * egbFixedChargeALargeRadius w φ τ ^ (3 : ℕ) * (1 + thermalRatio τ + thermalRatio τ ^ (2 : ℕ)) / 3 := by
  have hz := sub_pos.mpr (thermalRatio_lt_one τ)
  rw [egbFixedChargeAVolumeJump_formula]
  field_simp
  ring

theorem egbFixedChargeAEntropyJump_scaled_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAEntropyJump w φ τ / (1 - thermalRatio τ)) atBot
      (𝓝 (2 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ))) := by
  simp only [egbFixedChargeAEntropyJump_scaled_formula]
  have h : Tendsto (fun τ => Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ) *
      (1 + thermalRatio τ + 4 * egbFixedChargeACouplingWeight τ φ * (log (thermalRatio τ) / (thermalRatio τ - 1)))) atBot
      (𝓝 (Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) *
        (1 + (1 : ℝ) + 4 * egbFixedChargeACriticalCouplingWeight φ * 1))) :=
    (tendsto_const_nhds.mul ((egbFixedChargeALargeRadius_critical_limit w φ).pow 2)).mul
      ((tendsto_const_nhds.add thermalRatio_tendsto_atBot_one).add
        ((tendsto_const_nhds.mul (egbFixedChargeACouplingWeight_critical_limit φ)).mul egbFixedChargeA_log_secant_critical_limit))
  have he : Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) *
      (1 + (1 : ℝ) + 4 * egbFixedChargeACriticalCouplingWeight φ * 1) =
    2 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) := by ring
  rwa [he] at h

theorem egbFixedChargeAVolumeJump_scaled_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAVolumeJump w φ τ / (1 - thermalRatio τ)) atBot
      (𝓝 (4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (3 : ℕ))) := by
  simp only [egbFixedChargeAVolumeJump_scaled_formula]
  have hz := thermalRatio_tendsto_atBot_one
  have h : Tendsto (fun τ => 4 * Real.pi * egbFixedChargeALargeRadius w φ τ ^ (3 : ℕ) * (1 + thermalRatio τ + thermalRatio τ ^ (2 : ℕ)) / 3)
      atBot (𝓝 (4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (3 : ℕ) * (1 + (1 : ℝ) + 1 ^ (2 : ℕ)) / 3)) :=
    ((tendsto_const_nhds.mul ((egbFixedChargeALargeRadius_critical_limit w φ).pow 3)).mul
      ((tendsto_const_nhds.add hz).add (hz.pow 2))).div tendsto_const_nhds (by norm_num)
  have he : 4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (3 : ℕ) * (1 + (1 : ℝ) + 1 ^ (2 : ℕ)) / 3 =
    4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (3 : ℕ) := by ring
  rwa [he] at h

theorem egbFixedChargeA_latent_heat_scaled_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ / (1 - thermalRatio τ)) atBot
      (𝓝 (2 * egbFixedChargeACriticalRadius w φ / 3)) := by
  have h := (egbFixedChargeATemperature_critical_limit w φ).mul (egbFixedChargeAEntropyJump_scaled_critical_limit w φ)
  have he : egbFixedChargeACriticalTemperature w φ *
      (2 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) =
    2 * egbFixedChargeACriticalRadius w φ / 3 := by
    have hR := egbFixedChargeACriticalRadius_pos w φ
    have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
    unfold egbFixedChargeACriticalTemperature
    field_simp <;> ring
  rw [he] at h
  simpa only [mul_div_assoc] using h

theorem egbFixedChargeA_enthalpy_jump_scaled_critical_limit (w φ : ℝ) :
    Tendsto (fun τ =>
      (egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
       egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) /
        (1 - thermalRatio τ)) atBot (𝓝 (2 * egbFixedChargeACriticalRadius w φ / 3)) := by
  simp only [egbFixedChargeA_enthalpy_jump]
  exact egbFixedChargeA_latent_heat_scaled_critical_limit w φ

/-- A universal critical enthalpy coefficient measured against the actual radius separation. -/
theorem egbFixedChargeA_enthalpy_per_radius_gap_critical_limit (w φ : ℝ) :
    Tendsto (fun τ =>
      (egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
       egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) /
        egbFixedChargeARadiusGap w φ τ) atBot (𝓝 ((2 : ℝ) / 3)) := by
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have h := (egbFixedChargeA_enthalpy_jump_scaled_critical_limit w φ).div
    (egbFixedChargeARadiusGap_scaled_critical_limit w φ) hR.ne'
  have he : (2 * egbFixedChargeACriticalRadius w φ / 3) / egbFixedChargeACriticalRadius w φ = (2 : ℝ) / 3 := by
    field_simp
  rw [he] at h
  have hf : (fun τ =>
      ((egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
        egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) /
          (1 - thermalRatio τ)) / (egbFixedChargeARadiusGap w φ τ / (1 - thermalRatio τ))) =
    (fun τ =>
      (egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
       egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) /
        egbFixedChargeARadiusGap w φ τ) := by
    funext τ
    have hz := sub_pos.mpr (thermalRatio_lt_one τ)
    field_simp
  simp only [Pi.div_def] at h
  rw [hf] at h
  exact h

theorem egbFixedChargeACritical_mass_derivative (w φ : ℝ) :
    deriv (egbMass (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ))
      (egbFixedChargeACriticalRadius w φ) = (2 : ℝ) / 3 := by
  have h := (egbMass_explicit_derivative (egbFixedChargeACriticalPressure w φ) (exp w * cos φ)
    (exp w * sin φ) (egbFixedChargeACriticalLogScale w φ)).deriv
  rw [egbFixedChargeACriticalLogScale_exp] at h
  rw [h, egbFixedChargeACritical_charge_scaling, egbFixedChargeACriticalWeight_formula]
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  unfold egbFixedChargeACriticalPressure
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
