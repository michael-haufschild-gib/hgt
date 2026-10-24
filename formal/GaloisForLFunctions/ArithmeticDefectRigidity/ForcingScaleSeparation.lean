import GaloisForLFunctions.ArithmeticDefectRigidity.TheForcingDominatesTheReceiver

/-!
# Separation of the forcing and receiver scales

The actual receiver is negligible relative to its positive inversion forcing at every fixed
subcritical damping. This is a global energy statement; it does not follow from disappearance
of the forcing on fixed cells. The saving uses the actual Möbius source's zero-free region.
-/

open Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

private theorem tendsto_scaled_vkScale_atTop :
    Tendsto (fun x : ℝ => vkKappa * vkScale x / 270) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_vk_conditions (δ := 1) zero_lt_one (270 * b)] with x hx
  have h := hx.2.2.1
  rw [log_vkHeight] at h
  linarith

/-- The quantitative saving in the receiver-to-forcing comparison vanishes. -/
theorem tendsto_forcingRelativeSaving_zero :
    Tendsto (fun T : ℕ => Real.exp (-(vkKappa * vkScale T / 270))) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp
      (tendsto_scaled_vkScale_atTop.comp tendsto_natCast_atTop_atTop))

/-- The full forcing energy dominates the actual receiver by an unbounded relative factor. -/
theorem tendsto_receiver_div_forcingEnergy_zero (ε : SubcriticalDamping) :
    Tendsto (fun T => dampedMobiusEnergy ε T / forcingEnergy ε T) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_receiver_le_vk_mul_forcingEnergy ε
  have hlim := tendsto_forcingRelativeSaving_zero.const_mul C
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Filter.Eventually.of_forall fun T =>
    div_nonneg (dampedMobiusEnergy_nonneg ε T) (forcingEnergy_nonneg ε T)) ?_ hlim
  filter_upwards [hbound, eventually_ge_atTop 1] with T hT hT1
  have hF : 0 < forcingEnergy ε T := by
    cases T with
    | zero => omega
    | succ N => exact forcingEnergy_succ_pos ε N
  exact (div_le_iff₀ hF).mpr hT

/-- Forcing grows without bound even when receiver energy is admitted. -/
theorem tendsto_forcingEnergy_atTop (ε : SubcriticalDamping) :
    Tendsto (forcingEnergy ε) atTop atTop := by
  have ha : 0 < 1 - 2 * (ε : ℝ) := by linarith [ε.property.2]
  have hp := (tendsto_rpow_atTop ha).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop)
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hp.eventually_ge_atTop (b / forcingFloor ε)] with T hT
  have h := mul_le_mul_of_nonneg_left hT (forcingFloor_pos ε).le
  have hc : forcingFloor ε ≠ 0 := (forcingFloor_pos ε).ne'
  have hb : forcingFloor ε * (b / forcingFloor ε) = b := by field_simp
  rw [hb] at h
  exact h.trans (forcingFloor_mul_rpow_le ε T)

/-- The inversion identity makes the actual receiver nonzero at every positive horizon. -/
theorem receiverEnergy_succ_pos (ε : SubcriticalDamping) (T : ℕ) :
    0 < dampedMobiusEnergy ε (T + 1) := by
  have hE := dampedMobiusEnergy_nonneg (ε : ℝ) (T + 1)
  have hF := forcingEnergy_succ_pos ε T
  by_contra hnot
  have hzero : dampedMobiusEnergy ε (T + 1) = 0 :=
    le_antisymm (le_of_not_gt hnot) hE
  have hnorm := pronicNorm_inversionDefect_le_mul_sqrt_energy (ε : ℝ) (T + 1)
  rw [hzero, Real.sqrt_zero, mul_zero] at hnorm
  have heq : pronicNorm (T + 1) (inversionDefect ε) = 0 :=
    le_antisymm hnorm (pronicNorm_nonneg _ _)
  unfold forcingEnergy at hF
  rw [heq, zero_pow (by norm_num : 2 ≠ 0)] at hF
  exact (lt_irrefl 0) hF

/-- Receiver normalization makes the complete forcing energy diverge. -/
theorem tendsto_forcingEnergy_div_receiver_atTop (ε : SubcriticalDamping) :
    Tendsto (fun T => forcingEnergy ε T / dampedMobiusEnergy ε T) atTop atTop := by
  have hpos : ∀ᶠ T : ℕ in atTop, 0 < dampedMobiusEnergy ε T / forcingEnergy ε T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    cases T with
    | zero => omega
    | succ N => exact div_pos (receiverEnergy_succ_pos ε N) (forcingEnergy_succ_pos ε N)
  have h := Tendsto.inv_tendsto_nhdsGT_zero
    (tendsto_nhdsWithin_iff.mpr ⟨tendsto_receiver_div_forcingEnergy_zero ε, hpos⟩)
  exact h.congr' (Filter.Eventually.of_forall fun T => inv_div _ _)

end GaloisForLFunctions.ArithmeticDefectRigidity
