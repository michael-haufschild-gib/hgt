import GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyShift

/-!
# Removing a bounded exponential quotient in the half-plane Hardy space

Cauchy regularization first admits the bounded quotient into Hardy space.
Its boundary mass is controlled by the original function. The Paley–Wiener
representation sharpens every regularized bound, and dominated convergence
removes the regularizer.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The limiting boundary mass controls every interior line of a Hardy function. -/
theorem IsHalfPlaneHardy.of_boundary_mass_bound {F : ℂ → ℂ} {M N : ℝ}
    (hF : IsHalfPlaneHardy F M) {B : ℝ → ℝ}
    (hB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 N))
    (hbound : ∀ᶠ σ in 𝓝[>] (0 : ℝ),
      (∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ (2 : ℕ)) ≤ B σ) :
    IsHalfPlaneHardy F N := by
  let f := hardyDatum F hF
  have hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) := memLp_two_hardyDatum hF
  have he (σ : ℝ) (hσ : 0 < σ) :
      (∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ (2 : ℕ)) =
        ∫ ξ : ℝ, ‖laplaceRay f (rayLine σ ξ)‖ ^ (2 : ℕ) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by
      change ‖F (rayLine σ ξ)‖ ^ (2 : ℕ) = ‖laplaceRay f (rayLine σ ξ)‖ ^ (2 : ℕ)
      rw [isHalfPlaneHardy_eq_laplaceRay hF (by simpa using hσ)]
  have hlim : Tendsto (fun σ => ∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ (2 : ℕ))) := by
    apply (tendsto_integral_norm_sq_laplaceRay_line hf).congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (he σ hσ).symm
  have hmass : (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ (2 : ℕ)) ≤ N :=
    le_of_tendsto_of_tendsto hlim hB hbound
  refine ⟨hF.holo, hF.memLp, fun σ hσ => ?_⟩
  rw [he σ hσ]
  exact ((isHalfPlaneHardy_laplaceRay hf).bound σ hσ).trans hmass

private theorem norm_cauchyRegularizer_le {ε : ℝ} (hε : 0 ≤ ε)
    {w : ℂ} (hw : 0 < w.re) : ‖(1 + (ε : ℂ) * w)⁻¹‖ ≤ 1 := by
  have hre : 1 ≤ (1 + (ε : ℂ) * w).re := by
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact le_add_of_nonneg_right (mul_nonneg hε hw.le)
  have hn : 1 ≤ ‖1 + (ε : ℂ) * w‖ := hre.trans (re_le_norm _)
  rw [norm_inv]
  simpa only [inv_one] using inv_anti₀ (zero_lt_one : (0 : ℝ) < 1) hn

private theorem cauchyRegularizer_hardy {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, IsHalfPlaneHardy (fun w : ℂ => (1 + (ε : ℂ) * w)⁻¹) M := by
  have hc : 0 < ((ε⁻¹ : ℝ) : ℂ).re := by simpa using inv_pos.mpr hε
  refine ⟨_, (isHalfPlaneHardy_const_mul (isHalfPlaneHardy_inv_shift hc)
    ((ε⁻¹ : ℝ) : ℂ)).congr ?_⟩
  intro w hw
  have hεc : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hε.ne'
  rw [ofReal_inv, ← mul_inv_rev]
  congr 1
  field_simp
  ring

/-- A bounded analytic quotient obtained by removing a real delay retains the
original Hardy mass bound. -/
theorem isHalfPlaneHardy_exp_mul_of_bounded {F : ℂ → ℂ} {M C d : ℝ}
    (hF : IsHalfPlaneHardy F M)
    (hbd : ∀ w : ℂ, 0 < w.re → ‖Complex.exp ((d : ℂ) * w) * F w‖ ≤ C) :
    IsHalfPlaneHardy (fun w => Complex.exp ((d : ℂ) * w) * F w) M := by
  let Q : ℂ → ℂ := fun w => Complex.exp ((d : ℂ) * w) * F w
  have hQdiff : DifferentiableOn ℂ Q {w : ℂ | 0 < w.re} :=
    (Complex.differentiable_exp.comp
      ((differentiable_const _).mul differentiable_id)).differentiableOn.mul hF.holo
  have hQnorm (σ ξ : ℝ) : ‖Q (rayLine σ ξ)‖ =
      Real.exp (d * σ) * ‖F (rayLine σ ξ)‖ := by
    simp only [Q, norm_mul, norm_exp, mul_re, ofReal_re, ofReal_im,
      zero_mul, sub_zero, rayLine_re]
  have hQmem (σ : ℝ) (hσ : 0 < σ) : MemLp (fun ξ => Q (rayLine σ ξ)) 2 volume := by
    have hdom := (hF.memLp σ hσ).norm.const_mul (Real.exp (d * σ))
    have hline : Continuous (fun ξ : ℝ => Q (rayLine σ ξ)) :=
      hQdiff.continuousOn.comp_continuous (by unfold rayLine; fun_prop)
        (fun _ => by simpa using hσ)
    refine hdom.mono' hline.aestronglyMeasurable ?_
    exact Eventually.of_forall fun ξ => (hQnorm σ ξ).le
  have hQsq (σ : ℝ) (hσ : 0 < σ) :
      Integrable (fun ξ : ℝ => ‖Q (rayLine σ ξ)‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm (hQmem σ hσ).aestronglyMeasurable).mp (hQmem σ hσ)
  have hQmass (σ : ℝ) (hσ : 0 < σ) :
      (∫ ξ : ℝ, ‖Q (rayLine σ ξ)‖ ^ (2 : ℕ)) ≤ Real.exp (d * σ) ^ 2 * M := by
    simp only [hQnorm, mul_pow, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hF.bound σ hσ) (sq_nonneg _)
  let R : ℝ → ℂ → ℂ := fun ε w => Q w * (1 + (ε : ℂ) * w)⁻¹
  have hRnorm {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ) (ξ : ℝ) :
      ‖R ε (rayLine σ ξ)‖ ≤ ‖Q (rayLine σ ξ)‖ := by
    change ‖Q (rayLine σ ξ) * (1 + (ε : ℂ) * rayLine σ ξ)⁻¹‖ ≤ ‖Q (rayLine σ ξ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (norm_cauchyRegularizer_le hε (by simpa using hσ))
  have hR (ε : ℝ) (hε : 0 < ε) : IsHalfPlaneHardy (R ε) M := by
    obtain ⟨N, hN⟩ := cauchyRegularizer_hardy hε
    have h := isHalfPlaneHardy_mul_of_bounded hN hQdiff hbd
    have hR0 : IsHalfPlaneHardy (R ε) (C ^ 2 * N) :=
      h.congr (fun w _ => mul_comm _ _)
    apply hR0.of_boundary_mass_bound
      (B := fun σ => Real.exp (d * σ) ^ (2 : ℕ) * M)
    · have hc : Continuous (fun σ : ℝ => Real.exp (d * σ) ^ (2 : ℕ) * M) := by fun_prop
      simpa only [mul_zero, Real.exp_zero, one_pow, one_mul] using
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      apply le_trans _ (hQmass σ hσ)
      have hsq := (memLp_two_iff_integrable_sq_norm
        (hR0.memLp σ hσ).aestronglyMeasurable).mp (hR0.memLp σ hσ)
      apply integral_mono hsq (hQsq σ hσ)
      intro ξ
      exact pow_le_pow_left₀ (norm_nonneg _) (hRnorm hε.le hσ ξ) 2
  refine ⟨hQdiff, hQmem, fun σ hσ => ?_⟩
  have hlim : Tendsto (fun ε : ℝ => ∫ ξ : ℝ, ‖R ε (rayLine σ ξ)‖ ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ξ : ℝ, ‖Q (rayLine σ ξ)‖ ^ (2 : ℕ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun ξ : ℝ => ‖Q (rayLine σ ξ)‖ ^ (2 : ℕ))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((hR ε hε).memLp σ hσ).aestronglyMeasurable.norm.pow 2
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hRnorm hε.le hσ ξ) 2
    · exact hQsq σ hσ
    · exact Eventually.of_forall fun ξ => by
        have hc : ContinuousAt (fun ε : ℝ => R ε (rayLine σ ξ)) 0 := by
          dsimp only [R]
          apply continuousAt_const.mul
          apply ContinuousAt.inv₀
          · fun_prop
          · simp
        have ht : Tendsto (fun ε : ℝ => R ε (rayLine σ ξ)) (𝓝[>] (0 : ℝ))
            (𝓝 (Q (rayLine σ ξ))) := by
          simpa only [R, ofReal_zero, zero_mul, add_zero, inv_one, mul_one] using
            hc.tendsto.mono_left nhdsWithin_le_nhds
        exact ht.norm.pow 2
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hR ε hε).bound σ hσ

#print axioms isHalfPlaneHardy_exp_mul_of_bounded

end GaloisForLFunctions.HTGeometry
