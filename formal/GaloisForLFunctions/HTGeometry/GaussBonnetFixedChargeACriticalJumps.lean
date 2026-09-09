import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMonotonicity

/-!
# Vanishing phase discontinuities and the finite critical Clapeyron slope

The actual entropy, volume, and enthalpy discontinuities vanish at the
critical endpoint. Cancellation of their common radius-ratio gap gives
a finite, positive limit for the actual parametric pressure-temperature
slope, even though both jumps separately tend to zero.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbFixedChargeA_log_ratio_critical_limit :
    Tendsto (fun τ => log (thermalRatio τ)) atBot (𝓝 0) := by
  simpa only [log_one] using thermalRatio_tendsto_atBot_one.log one_ne_zero

theorem egbFixedChargeA_log_secant_critical_limit :
    Tendsto (fun τ => log (thermalRatio τ) / (thermalRatio τ - 1)) atBot (𝓝 1) := by
  have hz : Tendsto thermalRatio atBot (𝓝[≠] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨thermalRatio_tendsto_atBot_one,
      Filter.Eventually.of_forall (fun τ => (thermalRatio_lt_one τ).ne)⟩
  have h := (hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto_slope.comp hz
  simpa only [slope_def_field, Function.comp_def, log_one, sub_zero, inv_one] using h

theorem egbFixedChargeAEntropyJump_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAEntropyJump w φ) atBot (𝓝 0) := by
  change Tendsto (fun τ => egbFixedChargeAEntropyJump w φ τ) atBot (𝓝 0)
  simp only [egbFixedChargeAEntropyJump_formula]
  have h : Tendsto (fun τ => Real.pi * egbFixedChargeALargeRadius w φ τ ^ 2 *
      (1 - thermalRatio τ ^ 2 - 4 * egbFixedChargeACouplingWeight τ φ * log (thermalRatio τ))) atBot
      (𝓝 (Real.pi * egbFixedChargeACriticalRadius w φ ^ 2 *
        (1 - (1 : ℝ) ^ 2 - 4 * egbFixedChargeACriticalCouplingWeight φ * 0))) :=
    (tendsto_const_nhds.mul ((egbFixedChargeALargeRadius_critical_limit w φ).pow 2)).mul
      ((tendsto_const_nhds.sub (thermalRatio_tendsto_atBot_one.pow 2)).sub
        ((tendsto_const_nhds.mul (egbFixedChargeACouplingWeight_critical_limit φ)).mul
          egbFixedChargeA_log_ratio_critical_limit))
  norm_num at h
  exact h

theorem egbFixedChargeAVolumeJump_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAVolumeJump w φ) atBot (𝓝 0) := by
  change Tendsto (fun τ => egbFixedChargeAVolumeJump w φ τ) atBot (𝓝 0)
  simp only [egbFixedChargeAVolumeJump_formula]
  have h : Tendsto (fun τ => 4 * Real.pi * egbFixedChargeALargeRadius w φ τ ^ 3 * (1 - thermalRatio τ ^ 3) / 3)
      atBot (𝓝 (4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 3 * (1 - (1 : ℝ) ^ 3) / 3)) :=
    ((tendsto_const_nhds.mul ((egbFixedChargeALargeRadius_critical_limit w φ).pow 3)).mul
      (tendsto_const_nhds.sub (thermalRatio_tendsto_atBot_one.pow 3))).div tendsto_const_nhds (by norm_num)
  norm_num at h
  exact h

theorem egbFixedChargeA_latent_heat_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ) atBot (𝓝 0) := by
  simpa only [mul_zero] using (egbFixedChargeATemperature_critical_limit w φ).mul
    (egbFixedChargeAEntropyJump_critical_limit w φ)

theorem egbFixedChargeA_enthalpy_jump_critical_limit (w φ : ℝ) :
    Tendsto (fun τ =>
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ))
        atBot (𝓝 0) := by
  simp only [egbFixedChargeA_enthalpy_jump]
  exact egbFixedChargeA_latent_heat_critical_limit w φ

/-- Remove the common vanishing phase gap before taking the critical limit. -/
theorem egbFixedChargeAClapeyronSlope_secant_formula (w φ τ : ℝ) :
    egbFixedChargeAClapeyronSlope w φ τ =
      (3 / (4 * egbFixedChargeALargeRadius w φ τ)) *
        ((1 + thermalRatio τ) + 4 * egbFixedChargeACouplingWeight τ φ *
          (log (thermalRatio τ) / (thermalRatio τ - 1))) / (1 + thermalRatio τ + thermalRatio τ ^ 2) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hz := thermalRatio_pos τ
  have hzu := thermalRatio_lt_one τ
  have hn : thermalRatio τ - 1 ≠ 0 := by linarith
  have hp : 0 < 1 + thermalRatio τ + thermalRatio τ ^ 2 := by positivity
  have hcube : 1 - thermalRatio τ ^ 3 ≠ 0 := by
    have h := mul_pos (sub_pos.mpr hzu) hp
    nlinarith
  unfold egbFixedChargeAClapeyronSlope
  rw [egbFixedChargeAEntropyJump_formula, egbFixedChargeAVolumeJump_formula]
  field_simp
  ring

theorem egbFixedChargeAClapeyronSlope_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAClapeyronSlope w φ) atBot
      (𝓝 ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) / (2 * egbFixedChargeACriticalRadius w φ))) := by
  change Tendsto (fun τ => egbFixedChargeAClapeyronSlope w φ τ) atBot _
  simp only [egbFixedChargeAClapeyronSlope_secant_formula]
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have hz := thermalRatio_tendsto_atBot_one
  have h : Tendsto (fun τ => (3 / (4 * egbFixedChargeALargeRadius w φ τ)) *
      ((1 + thermalRatio τ) + 4 * egbFixedChargeACouplingWeight τ φ *
        (log (thermalRatio τ) / (thermalRatio τ - 1))) / (1 + thermalRatio τ + thermalRatio τ ^ 2)) atBot
      (𝓝 ((3 / (4 * egbFixedChargeACriticalRadius w φ)) *
        ((1 + (1 : ℝ)) + 4 * egbFixedChargeACriticalCouplingWeight φ * 1) / (1 + 1 + 1 ^ 2))) :=
    ((tendsto_const_nhds.div (tendsto_const_nhds.mul (egbFixedChargeALargeRadius_critical_limit w φ)) (by positivity)).mul
      ((tendsto_const_nhds.add hz).add
        ((tendsto_const_nhds.mul (egbFixedChargeACouplingWeight_critical_limit φ)).mul
          egbFixedChargeA_log_secant_critical_limit))).div
            ((tendsto_const_nhds.add hz).add (hz.pow 2)) (by norm_num)
  have he : (3 / (4 * egbFixedChargeACriticalRadius w φ)) *
      ((1 + (1 : ℝ)) + 4 * egbFixedChargeACriticalCouplingWeight φ * 1) / (1 + 1 + 1 ^ 2) =
    (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) / (2 * egbFixedChargeACriticalRadius w φ) := by
    field_simp <;> ring
  rwa [he] at h

theorem egbFixedChargeA_actual_slope_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => deriv (egbFixedChargeAPressure w φ) τ / deriv (egbFixedChargeATemperature w φ) τ)
      atBot (𝓝 ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) / (2 * egbFixedChargeACriticalRadius w φ))) := by
  simp only [egbFixedChargeA_clapeyron]
  exact egbFixedChargeAClapeyronSlope_critical_limit w φ

theorem egbFixedChargeA_critical_slope_pos (w φ : ℝ) :
    0 < (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) / (2 * egbFixedChargeACriticalRadius w φ) := by
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  positivity

end GaloisForLFunctions.HTGeometry
