import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreQuadraticContactWidthLoss

/-!
# Unconditional decay of the literal quadratic-contact residual

The aligned energy gives an exact fourth-power normalization of the completed
amplitude. PNT cancellation then makes the quadratic-contact residual sublinear.
This supplies no fixed power saving and no narrower zero strip.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem suzukiQuadraticContactResidual_eq_core_mul_energyRatio_sq (N : ℕ) :
    suzukiTransitionCoreQuadraticContactResidual N =
      suzukiNaturalApertureTransitionCoreCauchyEnergy N *
        (suzukiTransitionCoreAlignedGammaCompletedEnergy N /
          suzukiNaturalApertureTransitionCoreCauchyEnergy N) ^ 2 := by
  rw [suzukiTransitionCoreQuadraticContactResidual]
  split_ifs with hC
  · simp [hC]
  · field_simp

theorem suzukiQuadraticContactResidual_div_core_eq_energyRatio_sq (N : ℕ) :
    suzukiTransitionCoreQuadraticContactResidual N /
        suzukiNaturalApertureTransitionCoreCauchyEnergy N =
      (suzukiTransitionCoreAlignedGammaCompletedEnergy N /
        suzukiNaturalApertureTransitionCoreCauchyEnergy N) ^ 2 := by
  by_cases hC : suzukiNaturalApertureTransitionCoreCauchyEnergy N = 0
  · simp [hC]
  · rw [suzukiQuadraticContactResidual_eq_core_mul_energyRatio_sq]
    field_simp

/-- The identity includes the totalized zero-charge and zero-core cases. -/
theorem suzukiQuadraticContactResidual_eq_core_mul_completedRatio_fourth (N : ℕ) :
    suzukiTransitionCoreQuadraticContactResidual N =
      suzukiNaturalApertureTransitionCoreCauchyEnergy N *
        (suzukiNaturalApertureCompletedLowerHardyAmplitude N /
          unitRieszCoherentPrimeOutgoingCharge N) ^ 4 := by
  by_cases hC : suzukiNaturalApertureTransitionCoreCauchyEnergy N = 0
  · simp [suzukiTransitionCoreQuadraticContactResidual, hC]
  · by_cases hA : unitRieszCoherentPrimeOutgoingCharge N = 0
    · simp [suzukiTransitionCoreQuadraticContactResidual,
        suzukiTransitionCoreAlignedGammaCompletedEnergy, hC, hA]
    · rw [suzukiTransitionCoreQuadraticContactResidual, dif_neg hC,
        suzukiTransitionCoreAlignedGammaCompletedEnergy, dif_neg hA]
      field_simp

theorem tendsto_suzukiQuadraticContactResidual_div_core_atTop_zero :
    Tendsto (fun N : ℕ => suzukiTransitionCoreQuadraticContactResidual N /
      suzukiNaturalApertureTransitionCoreCauchyEnergy N) atTop (𝓝 0) := by
  simp_rw [suzukiQuadraticContactResidual_div_core_eq_energyRatio_sq]
  simpa using tendsto_suzukiAlignedEnergy_div_transitionCore_atTop_zero.pow 2

/-- The actual residual is `o(N)`, without a zero-width hypothesis. -/
theorem tendsto_suzukiQuadraticContactResidual_div_nat_atTop_zero :
    Tendsto (fun N : ℕ =>
      suzukiTransitionCoreQuadraticContactResidual N / (N : ℝ)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun N : ℕ => suzukiTransitionCoreLinearEnvelope *
      (suzukiTransitionCoreAlignedGammaCompletedEnergy N /
        suzukiNaturalApertureTransitionCoreCauchyEnergy N) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_suzukiAlignedEnergy_div_transitionCore_atTop_zero.pow 2).const_mul
      suzukiTransitionCoreLinearEnvelope
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
    (suzukiTransitionCoreQuadraticContactResidual_nonneg N) hN0.le),
    suzukiQuadraticContactResidual_eq_core_mul_energyRatio_sq]
  have hcore : suzukiNaturalApertureTransitionCoreCauchyEnergy N / (N : ℝ) ≤
      suzukiTransitionCoreLinearEnvelope := by
    apply (div_le_iff₀ hN0).2
    exact suzukiNaturalApertureTransitionCoreCauchyEnergy_le_linear N
  calc
    _ = (suzukiNaturalApertureTransitionCoreCauchyEnergy N / (N : ℝ)) *
        (suzukiTransitionCoreAlignedGammaCompletedEnergy N /
          suzukiNaturalApertureTransitionCoreCauchyEnergy N) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcore (sq_nonneg _)

end

end GaloisForLFunctions.RHTower
