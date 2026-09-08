import GaloisForLFunctions.HTGeometry.UnitWaveSine
/-! Retarded convolution with the genuine physical sine propagator. -/
open MeasureTheory Set Filter
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section

def unitWaveDuhamel (F : ℝ → FourierRealL2) (τ : ℝ) : FourierRealL2 :=
  ∫ σ in (0:ℝ)..τ, unitWaveSine (τ-σ) (F σ)

theorem unitWaveDuhamel_continuous (F : ℝ → FourierRealL2) (hF : Continuous F) :
    Continuous (unitWaveDuhamel F) := by
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous ?_ continuous_id
  exact unitWaveSine_continuous_comp _ _ (continuous_fst.sub continuous_snd)
    (hF.comp continuous_snd)

theorem unitWaveDuhamel_zero_of_nonpos (F : ℝ → FourierRealL2)
    (hF : ∀ τ, τ ≤ 0 → F τ = 0) (τ : ℝ) (hτ : τ ≤ 0) : unitWaveDuhamel F τ = 0 := by
  unfold unitWaveDuhamel
  calc
    _ = ∫ σ in (0:ℝ)..τ, (0:FourierRealL2) := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      have hσ₀ : σ ≤ 0 := by rw [uIcc_of_ge hτ] at hσ; exact hσ.2
      change unitWaveSine (τ-σ) (F σ) = 0
      rw [hF σ hσ₀,map_zero]
    _ = 0 := intervalIntegral.integral_zero

/-- The entire forced free evolution is bounded by the total actual source norm. -/
theorem unitWaveDuhamel_norm_le (F : ℝ → FourierRealL2) (hF : Continuous F)
    (hi : IntegrableOn F (Ioi 0)) (hz : ∀ τ, τ ≤ 0 → F τ = 0) (τ : ℝ) :
    ‖unitWaveDuhamel F τ‖ ≤ (2*Real.pi)⁻¹*(∫ σ in Ioi (0:ℝ), ‖F σ‖) := by
  have hc : 0 ≤ (2*Real.pi)⁻¹ := by positivity
  by_cases hτ : τ ≤ 0
  · rw [unitWaveDuhamel_zero_of_nonpos F hz τ hτ,norm_zero]
    exact mul_nonneg hc (integral_nonneg (fun _ => norm_nonneg _))
  · have hτ₀ := le_of_lt (lt_of_not_ge hτ)
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ)) (b := τ) hτ₀
      (f := fun σ => unitWaveSine (τ-σ) (F σ))
      (g := fun σ => (2*Real.pi)⁻¹*‖F σ‖)
      (Eventually.of_forall (fun σ _ => unitWaveSine_apply_norm_le (τ-σ) (F σ)))
      ((continuous_const.mul hF.norm).intervalIntegrable 0 τ)
    change ‖unitWaveDuhamel F τ‖ ≤ _ at hb
    refine hb.trans ?_
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le hτ₀]
    apply mul_le_mul_of_nonneg_left _ hc
    exact setIntegral_mono_set hi.norm (Eventually.of_forall (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun _ h => h.1))

/-- Convolution preserves the exact odd constraint, with no pointwise representative assumptions. -/
theorem unitWaveDuhamel_reflection (F : ℝ → FourierRealL2) (hF : Continuous F)
    (ho : ∀ τ, l2Reflection (F τ) = -F τ) (τ : ℝ) :
    l2Reflection (unitWaveDuhamel F τ) = -unitWaveDuhamel F τ := by
  have hi := (unitWaveSine_continuous_comp (fun σ => τ-σ) F
    (continuous_const.sub continuous_id) hF).intervalIntegrable (μ := volume) 0 τ
  unfold unitWaveDuhamel
  rw [← l2Reflection.intervalIntegral_comp_comm hi,← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro σ _
  change l2Reflection (unitWaveSine (τ-σ) (F σ)) = -unitWaveSine (τ-σ) (F σ)
  rw [← unitWaveSine_reflection,ho,map_neg]

end
end GaloisForLFunctions.HTGeometry
