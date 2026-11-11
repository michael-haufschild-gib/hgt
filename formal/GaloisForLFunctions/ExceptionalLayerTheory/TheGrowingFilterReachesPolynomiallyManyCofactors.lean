import GaloisForLFunctions.ExceptionalLayerTheory.TheGrowingGaussianErrorSurvivesTheFilter
import GaloisForLFunctions.ExceptionalLayerTheory.TheGrowingCofactorTailSurvivesTheFilter

/-!
# Growing filters and polynomial cofactor localization

The actual prime current, with its continuum pole removed, differs from
the short centred cofactor current by two holomorphic errors. Their
separate filter bounds preserve the full spacing power and both signed
continuum corrections.
-/

open Complex Filter Topology ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The Mellin-twisted difference between the actual prime current and its
finite cofactor reduction, including both signed continuum corrections. -/
def twistedGaussianHigherCofactorReductionError (r : ℕ) (β t : ℝ) (U V W : ℕ)
    (ε z : ℂ) : ℂ :=
  Complex.exp ((((1 / 2 : ℂ) + t * I) - β) * z) *
    (((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r
        (1 / 2) t (ε * Complex.exp (-2 * z)) n) -
      gaussianHigherMomentPole r ((1 / 2 : ℂ) + t * I)
        (ε * Complex.exp (-2 * z)) t) -
      gaussianHigherCentredVaughanCofactorCurrent r (1 / 2) t
        (ε * Complex.exp (-2 * z)) U V W)

/-- Arithmetic reduction and cofactor truncation are the two exact errors. -/
theorem twistedGaussianHigherCofactorReductionError_eq (r : ℕ) (β : ℝ)
    {t : ℝ} (ht : 0 < t) (U V W : ℕ) {ε z : ℂ}
    (hε : 0 < (ε * Complex.exp (-2 * z)).re)
    (hsector : ‖ε * Complex.exp (-2 * z)‖ ≤
      4 * (ε * Complex.exp (-2 * z)).re * t) :
    twistedGaussianHigherCofactorReductionError r β t U V W ε z =
      twistedGaussianHigherCentredVaughanError r β t U V ε z +
        twistedGaussianHigherVaughanCofactorTail r β t U V W ε z := by
  have he := gaussianHigherCentredVaughan_sub_cofactorCurrent_eq r
    (by norm_num : (0 : ℝ) ≤ 1 / 2) ht hε hsector U V W
  unfold twistedGaussianHigherCofactorReductionError
    twistedGaussianHigherCentredVaughanError twistedGaussianHigherVaughanCofactorTail
    gaussianHigherCentredVaughanError
  rw [← he]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- A filter of degree `O(t/log t)` transfers the actual prime current to
at most `3t^71` cofactors with exponentially small spacing-normalized error. -/
theorem eventually_growingFilter_polynomialCofactorReduction {a β : ℝ}
    (ha : 0 < a) (hβ : 1 / 2 ≤ β) :
    ∀ᶠ t : ℝ in atTop,
      (gaussianGrowingCofactorCutoff 68 t : ℝ) ≤ 3 * t ^ 71 ∧
      ∀ α ξ h B : ℝ, 0 < α → 2 * α ≤ ξ → ξ ≤ α * t →
        α * Real.exp (a * t) ^ 2 = 2 → 0 ≤ h → 0 ≤ B →
        B + |gaussianCofactorTwist (1 / 2) β ⌊t⌋₊| ≤ t ^ 2 →
        h * (B + |gaussianCofactorTwist (1 / 2) β ⌊t⌋₊|) ≤ 1 →
        ∀ ws : List ℂ, (∀ ω ∈ ws, ‖ω‖ ≤ B) →
          (ws.length : ℝ) * Real.log t ≤ (a / 24) * t →
          ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
            (dampingFilterPolynomial h ws).coeff j *
              twistedGaussianHigherCofactorReductionError
                (gaussianGrowingMomentOrder (a / 64) t) β t
                (gaussianGrowingLongCutoff a 68 t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff 68 t)
                ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
            2 * h ^ ws.length * Real.exp (-(a / 8) * t) := by
  filter_upwards [eventually_filtered_gaussianHigherCentredVaughanError_decay ha hβ,
    eventually_filtered_gaussianHigherVaughanCofactorTail_decay (β := β) ha,
    eventually_gaussianGrowingCofactorCutoff_bounds ha 68,
    eventually_ge_atTop (4 : ℝ)] with t hmain htail hcut ht
  refine ⟨hcut.2, ?_⟩
  intro α ξ h B hα hlo hhi hscale hh hB hBt hhB ws hws hdegree
  have ht0 : 0 < t := by linarith only [ht]
  have hBt' : B ≤ t ^ 2 := by
    linarith only [hBt, (abs_nonneg (gaussianCofactorTwist (1 / 2) β ⌊t⌋₊))]
  have hhB' : h * B ≤ 1 := by
    have hh' := mul_nonneg hh (abs_nonneg (gaussianCofactorTwist (1 / 2) β ⌊t⌋₊))
    nlinarith only [hhB, hh']
  have HM := hmain α ξ h B hα hlo hhi hscale hh hB hBt' hhB' ws hws hdegree
  have HT := htail α ξ h B hα hlo hhi hscale hh hB hBt hhB ws hws hdegree
  have he (j : ℕ) : twistedGaussianHigherCofactorReductionError
      (gaussianGrowingMomentOrder (a / 64) t) β t
      (gaussianGrowingLongCutoff a 68 t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff 68 t)
      ((α : ℂ) - ξ * I) ((j : ℂ) * h) =
        twistedGaussianHigherCentredVaughanError (gaussianGrowingMomentOrder (a / 64) t)
          β t (gaussianGrowingLongCutoff a 68 t) ⌊t⌋₊ ((α : ℂ) - ξ * I) ((j : ℂ) * h) +
        twistedGaussianHigherVaughanCofactorTail (gaussianGrowingMomentOrder (a / 64) t)
          β t (gaussianGrowingLongCutoff a 68 t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff 68 t)
          ((α : ℂ) - ξ * I) ((j : ℂ) * h) := by
    obtain ⟨hε, hεlo, hεhi, Y, hY, hscaleY, hYlo⟩ :=
      exists_damping_rotated_scale hα ht hlo hhi
        (show t * |((j : ℂ) * h).im| ≤ 1 / 16 by simp)
        (Real.exp_pos (a * t)) hscale
    apply twistedGaussianHigherCofactorReductionError_eq _ β ht0 _ _ _ hε
    have hn := Complex.norm_le_abs_re_add_abs_im
      (((α : ℂ) - ξ * I) * Complex.exp (-2 * ((j : ℂ) * h)))
    rw [abs_of_pos hε, abs_of_nonpos (by linarith only [hεlo, hε])] at hn
    have hm := mul_le_mul_of_nonneg_left ht hε.le
    nlinarith only [hn, hεhi, hm, hε]
  simp_rw [he, mul_add, Finset.sum_add_distrib]
  exact (norm_add_le _ _).trans ((add_le_add HM HT).trans_eq (by ring))

end GaloisForLFunctions.ExceptionalLayerTheory
