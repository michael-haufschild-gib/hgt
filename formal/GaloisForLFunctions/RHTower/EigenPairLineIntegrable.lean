import GaloisForLFunctions.RHTower.XiQuotientRealDecay

/-!
# Integrability of the eigen-pair product along horizontal lines

On any horizontal line inside the unit substrip, the product of a removable eigen quotient with
the conjugate-reflected quotient of a second zero is integrable: each factor obeys the
exponential substrip bound (18a), so the product is dominated by a two-sided decaying
exponential.

This is the integrable-weight input for the termwise von Mangoldt swap and the Fourier-inversion
step of the eigen-pair assembly.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex

/-- **Eigen-pair line integrability.**  For zeros `α, β` and a line height `|Y| ≤ A < 1`, the
pair product `t ↦ F_α(t − iY)·conj(F_β(t + iY))` is integrable, with both factors dominated by
the substrip bound (18a) at rate `δ`. -/
theorem integrable_eigenPair_line {α β : ℂ}
    (hα : XiC α = 0) (hβ : XiC β = 0)
    {A δ Y : ℝ} (hA0 : 0 ≤ A) (hA1 : A < 1) (hδ0 : 0 < δ)
    (hδ4 : 2 * δ < Real.pi / 2) (hY : |Y| ≤ A) :
    Integrable (fun t : ℝ =>
      xiThetaEigenFourier α ((t : ℂ) + ((-Y : ℝ) : ℂ) * Complex.I) *
        (starRingEnd ℂ)
          (xiThetaEigenFourier β ((t : ℂ) + (Y : ℂ) * Complex.I))) := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_norm_xiThetaEigenFourier_horizontal_le hα hA0 hA1 hδ0.le hδ4
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_norm_xiThetaEigenFourier_horizontal_le hβ hA0 hA1 hδ0.le hδ4
  have hbase : Integrable (fun t : ℝ => Real.exp (-(2 * δ) * |t|)) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_abs 0 (by linarith : (0 : ℝ) < 2 * δ)
  refine Integrable.mono' (hbase.const_mul (C₁ * C₂)) ?_ ?_
  · exact (((continuous_xiThetaEigenFourier α).comp
        (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + ((-Y : ℝ) : ℂ) * Complex.I)).mul
      (Complex.continuous_conj.comp
        ((continuous_xiThetaEigenFourier β).comp
          (by fun_prop :
            Continuous fun t : ℝ => (t : ℂ) + (Y : ℂ) * Complex.I)))).aestronglyMeasurable
  · filter_upwards with t
    have hY' : |(-Y : ℝ)| ≤ A := by rwa [abs_neg]
    have hb₁ := h₁ t (-Y) hY'
    have hb₂ := h₂ t Y hY
    calc ‖xiThetaEigenFourier α ((t : ℂ) + ((-Y : ℝ) : ℂ) * Complex.I) *
          (starRingEnd ℂ) (xiThetaEigenFourier β ((t : ℂ) + (Y : ℂ) * Complex.I))‖
        = ‖xiThetaEigenFourier α ((t : ℂ) + ((-Y : ℝ) : ℂ) * Complex.I)‖ *
            ‖xiThetaEigenFourier β ((t : ℂ) + (Y : ℂ) * Complex.I)‖ := by
          rw [norm_mul, RCLike.norm_conj]
      _ ≤ (C₁ * Real.exp (-(δ * |t|))) * (C₂ * Real.exp (-(δ * |t|))) := by
          exact mul_le_mul hb₁ hb₂ (norm_nonneg _)
            (mul_nonneg hC₁ (Real.exp_pos _).le)
      _ = C₁ * C₂ * Real.exp (-(2 * δ) * |t|) := by
          rw [show (-(2 * δ) * |t| : ℝ) = -(δ * |t|) + -(δ * |t|) by ring, Real.exp_add]
          ring


end

end RHTower
