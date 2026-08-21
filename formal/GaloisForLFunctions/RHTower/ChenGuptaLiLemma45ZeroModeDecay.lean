/-
# Chen--Gupta--Li Lemma 4.5 zero-mode Fourier decay

Formalizes the two analytic estimates used in the final `Z'` step of CGL
Lemma 4.5: an order-zero bound for arbitrary coordinate differences and an
arbitrary-order reciprocal bound when a positive ordinate gap is certified.
The gap is carried as data, not supplied as an undischarged proof premise.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45ZeroMode
import GaloisForLFunctions.RHTower.ChenGuptaLiHtReciprocalAllOrder

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- A literal time difference with a certified positive lower gap. -/
structure CGLLemma45SeparatedDifference where
  difference : ℝ
  spacing : ℝ
  spacing_pos : 0 < spacing
  spacing_le_abs : spacing ≤ |difference|

/-- The explicit all-order reciprocal Fourier budget is nonnegative. -/
theorem cglLogFourierAmplitudeAllOrderBudget_nonneg (w : CGLSmoothBump) (n : ℕ) :
    0 ≤ cglLogFourierAmplitudeAllOrderBudget w n := by
  unfold cglLogFourierAmplitudeAllOrderBudget
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · exact cglLogPhasePolynomialBudget_nonneg _
  · exact MeasureTheory.integral_nonneg fun _ => norm_nonneg _

/-- Every zero-frequency CGL coordinate has the closed order-zero Fourier
budget from Lemma 4.3. -/
theorem norm_cglLemma45ZeroModePairAmplitude_le_uniform
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) :
    ‖cglLemma45ZeroModePairAmplitude w N Q t‖ ≤
      cglAffineFourierScale N Q * cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 := by
  have hfourier := cglSmoothBumpHt_allOrder_reciprocalParameter_fourier_decay
    w.toCGLSmoothBump 0 t 0
  have hfourier' : ‖𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) 0‖ ≤
      cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 := by
    simpa using hfourier
  unfold cglLemma45ZeroModePairAmplitude
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cglAffineFourierScale_pos N Q)]
  exact mul_le_mul_of_nonneg_left hfourier' (cglAffineFourierScale_pos N Q).le

/-- A certified same-character ordinate gap converts CGL Lemma 4.3(2) into
an arbitrary-order zero-frequency bound for one Poisson coordinate. -/
theorem norm_cglLemma45ZeroModePairAmplitude_le_reciprocal
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (n : ℕ) (d : CGLLemma45SeparatedDifference) :
    ‖cglLemma45ZeroModePairAmplitude w N Q d.difference‖ ≤
      cglAffineFourierScale N Q *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / d.spacing ^ n) := by
  have hsource := cglSmoothBumpHt_allOrder_reciprocalParameter_fourier_decay
    w.toCGLSmoothBump n d.difference 0
  have hsource' : |d.difference| ^ n *
      ‖𝓕 (cglSmoothBumpHt w.toCGLSmoothBump d.difference : ℝ → ℂ) 0‖ ≤
      cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n := by
    simpa using hsource
  have hpow : d.spacing ^ n ≤ |d.difference| ^ n :=
    pow_le_pow_left₀ d.spacing_pos.le d.spacing_le_abs n
  have hpowpos : 0 < d.spacing ^ n := pow_pos d.spacing_pos _
  have hfourier : ‖𝓕 (cglSmoothBumpHt w.toCGLSmoothBump d.difference : ℝ → ℂ) 0‖ ≤
      cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / d.spacing ^ n := by
    calc
      ‖𝓕 (cglSmoothBumpHt w.toCGLSmoothBump d.difference : ℝ → ℂ) 0‖ =
          (d.spacing ^ n * ‖𝓕 (cglSmoothBumpHt w.toCGLSmoothBump d.difference : ℝ → ℂ) 0‖) /
            d.spacing ^ n := by field_simp
      _ ≤ (|d.difference| ^ n *
          ‖𝓕 (cglSmoothBumpHt w.toCGLSmoothBump d.difference : ℝ → ℂ) 0‖) /
            d.spacing ^ n := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hpowpos.le
      _ ≤ _ := div_le_div_of_nonneg_right hsource' hpowpos.le
  unfold cglLemma45ZeroModePairAmplitude
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cglAffineFourierScale_pos N Q)]
  exact mul_le_mul_of_nonneg_left hfourier (cglAffineFourierScale_pos N Q).le

end RHTower
