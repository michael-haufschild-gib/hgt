import GaloisForLFunctions.HTGeometry.HerglotzJetMap

/-!
# Continuity of the Herglotz jet map

The countable Baire step needs each degeneracy locus to be closed, hence needs the jet map to be
continuous in the parameter.

Continuity is quantitative here.  On the unit ball around a base parameter the exponential is
Lipschitz with constant `2 exp u₀`, so the jet map is Lipschitz with an explicit constant built from
the uniform kernel bound and the integral of the base density.  No compactness or dominated
convergence argument is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponential is Lipschitz on unit-length increments, with constant twice its base value. -/
theorem abs_exp_sub_exp_le {a b : ℝ} (h : |a - b| ≤ 1) :
    |Real.exp a - Real.exp b| ≤ 2 * Real.exp b * |a - b| := by
  have hfac : Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    ring_nf
  rw [hfac, abs_mul, abs_of_pos (Real.exp_pos b)]
  have hstep := Real.abs_exp_sub_one_le h
  have hpos : 0 < Real.exp b := Real.exp_pos b
  calc Real.exp b * |Real.exp (a - b) - 1|
      ≤ Real.exp b * (2 * |a - b|) :=
        mul_le_mul_of_nonneg_left hstep (le_of_lt hpos)
    _ = 2 * Real.exp b * |a - b| := by ring

set_option linter.unusedSectionVars false in
/-- **Quantitative continuity of the jet map.**  On unit-length parameter increments each jet
coordinate moves by at most an explicit multiple of the parameter increment. -/
theorem norm_herglotzJetMap_sub_le (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (u₀ u : Lp ℝ ⊤ μ) (hclose : ‖u - u₀‖ ≤ 1) (s : jetIndex n) :
    ‖herglotzJetMap μ w x n u s - herglotzJetMap μ w x n u₀ s‖ ≤
      (2 * cauchyJetKernelBound x n s *
        ∫ t, Real.exp (u₀ t) * |w t| ∂μ) * ‖u - u₀‖ := by
  have hIu := integrable_weight_mul_cauchyJetKernel μ
    (fun t => Real.exp (u t) * w t) (integrable_exp_Lp_top_mul μ u w hw) x hne n s
  have hIu₀ := integrable_weight_mul_cauchyJetKernel μ
    (fun t => Real.exp (u₀ t) * w t) (integrable_exp_Lp_top_mul μ u₀ w hw) x hne n s
  have hdom : Integrable
      (fun t => 2 * cauchyJetKernelBound x n s * ‖u - u₀‖ *
        (Real.exp (u₀ t) * |w t|)) μ :=
    (integrable_exp_Lp_top_mul μ u₀ _ hw.abs).const_mul _
  have hbound : ∀ᵐ t ∂μ,
      ‖((Real.exp (u t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s -
        ((Real.exp (u₀ t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s‖ ≤
        2 * cauchyJetKernelBound x n s * ‖u - u₀‖ *
          (Real.exp (u₀ t) * |w t|) := by
    filter_upwards [ae_norm_le_norm_Lp_top μ (u - u₀), Lp.coeFn_sub u u₀]
      with t ht hsub
    have hdiff : |u t - u₀ t| ≤ ‖u - u₀‖ := by
      have : ((u - u₀) t) = u t - u₀ t := by rw [hsub]; simp
      rw [← this]
      simpa [Real.norm_eq_abs] using ht
    have hone : |u t - u₀ t| ≤ 1 := le_trans hdiff hclose
    have hexp := abs_exp_sub_exp_le hone
    have hker := norm_cauchyJetKernel_le x hne n s t
    have hfac : ((Real.exp (u t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s -
        ((Real.exp (u₀ t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s =
        (((Real.exp (u t) - Real.exp (u₀ t)) * w t : ℝ) : ℂ) *
          cauchyJetKernel x n t s := by
      push_cast
      ring
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hstep : |Real.exp (u t) - Real.exp (u₀ t)| * |w t| *
        ‖cauchyJetKernel x n t s‖ ≤
        (2 * Real.exp (u₀ t) * ‖u - u₀‖) * |w t| *
          cauchyJetKernelBound x n s := by
      apply mul_le_mul _ hker (norm_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact le_trans hexp
        (mul_le_mul_of_nonneg_left hdiff (by positivity))
    calc |Real.exp (u t) - Real.exp (u₀ t)| * |w t| *
          ‖cauchyJetKernel x n t s‖
        ≤ (2 * Real.exp (u₀ t) * ‖u - u₀‖) * |w t| *
            cauchyJetKernelBound x n s := hstep
      _ = 2 * cauchyJetKernelBound x n s * ‖u - u₀‖ *
            (Real.exp (u₀ t) * |w t|) := by ring
  show ‖(∫ t, ((Real.exp (u t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ) -
      ∫ t, ((Real.exp (u₀ t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ‖ ≤ _
  rw [← integral_sub hIu hIu₀]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => norm_nonneg _) hdom hbound) ?_
  rw [integral_const_mul]
  ring_nf
  exact le_refl _

end

end GaloisForLFunctions.HTGeometry
