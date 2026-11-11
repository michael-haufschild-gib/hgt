import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheSublogarithmicGridsHaveVanishingNormalizedDensity
import GaloisForLFunctions.SurfaceOfSpecZ.TheTraceZetaFunctionAtThePowerDegrees

/-!
# Positive calibrated blocks survive spline smoothing

The eighth box convolution is a nonnegative probability density supported
on `[-8,8]`. Positivity on a window enlarged by eight therefore gives a
positive spline trace on the original window, even after a common real
exponential shift.
-/

open Complex Finset MeasureTheory Set
open GaloisForLFunctions.SquareRootThreshold Zeta23 RHTower.WeilDeletion

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The squared transform of the cubic box spline, applied to a finite exponential block. -/
def splineExponentialBlock {ι : Type*} [Fintype ι] (w : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ j, sincC (-I * w j) ^ 8 * Complex.exp (w j * (t : ℂ))

private theorem spline_exponential_integrable (w : ℂ) (t : ℝ) :
    Integrable (fun u : ℝ => (upow 1 7 u : ℂ) * Complex.exp (w * ((t + u : ℝ) : ℂ))) := by
  have hi := (integrable_ofReal_mul_exp (integrable_upow 1 7)
    (hasCompactSupport_upow 1 7) (-I * w)).const_mul (Complex.exp (w * (t : ℂ)))
  convert hi using 1
  funext u
  have he : I * (-I * w) * (u : ℂ) = w * (u : ℂ) := by
    rw [← mul_assoc I (-I), mul_neg, I_mul_I]
    ring
  rw [he, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

private theorem integral_spline_exponential (w : ℂ) (t : ℝ) :
    (∫ u : ℝ, (upow 1 7 u : ℂ) * Complex.exp (w * ((t + u : ℝ) : ℂ))) =
      sincC (-I * w) ^ 8 * Complex.exp (w * (t : ℂ)) := by
  have he (u : ℝ) : (upow 1 7 u : ℂ) * Complex.exp (w * ((t + u : ℝ) : ℂ)) =
      ((upow 1 7 u : ℂ) * Complex.exp (I * (-I * w) * (u : ℂ))) * Complex.exp (w * (t : ℂ)) := by
    have hh : I * (-I * w) * (u : ℂ) = w * (u : ℂ) := by
      rw [← mul_assoc I (-I), mul_neg, I_mul_I]
      ring
    rw [hh, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hf := paperFT_boxSpline_eq 7 (-I * w)
  change (∫ u : ℝ, (upow 1 7 u : ℂ) * Complex.exp (I * (-I * w) * (u : ℂ))) =
    sincC (-I * w) ^ 8 at hf
  rw [hf]

/-- Spline smoothing is integration against a positive unit-mass kernel. -/
theorem splineExponentialBlock_re_eq_integral {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (t : ℝ) :
    (splineExponentialBlock w t).re =
      ∫ u : ℝ, upow 1 7 u * (∑ j, Complex.exp (w j * ((t + u : ℝ) : ℂ))).re := by
  classical
  have hi : Integrable (fun u : ℝ => ∑ j, (upow 1 7 u : ℂ) *
      Complex.exp (w j * ((t + u : ℝ) : ℂ))) :=
    integrable_finset_sum _ (fun j _ => spline_exponential_integrable (w j) t)
  have he : (∫ u : ℝ, ∑ j, (upow 1 7 u : ℂ) *
      Complex.exp (w j * ((t + u : ℝ) : ℂ))) = splineExponentialBlock w t := by
    rw [integral_finset_sum _ (fun j _ => spline_exponential_integrable (w j) t)]
    simp only [integral_spline_exponential, splineExponentialBlock]
  rw [← he, ← Complex.reCLM.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Complex.reCLM_apply, ← Finset.mul_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A positive calibrated block remains positive after the spline multiplier is applied. -/
theorem splineExponentialBlock_re_ge_of_positive_window {ι : Type*} [Fintype ι]
    (z : ι → ℂ) {x T R v : ℝ} (hx : 0 ≤ x) (hv : |v| ≤ R)
    (hpos : ∀ a : ℝ, |a| ≤ R + 8 →
      (3 / 4 : ℝ) ≤ (∑ j, Complex.exp (((T + a : ℝ) : ℂ) * z j)).re) :
    (3 / 4 : ℝ) * Real.exp (x * (T + v - 8)) ≤
      (splineExponentialBlock (fun j => (x : ℂ) + z j) (T + v)).re := by
  classical
  let w : ι → ℂ := fun j => (x : ℂ) + z j
  let c : ℝ := (3 / 4) * Real.exp (x * (T + v - 8))
  have hi : Integrable (fun u : ℝ => ∑ j, (upow 1 7 u : ℂ) *
      Complex.exp (w j * ((T + v + u : ℝ) : ℂ))) :=
    integrable_finset_sum _ (fun j _ => spline_exponential_integrable (w j) (T + v))
  have hir : Integrable (fun u : ℝ => upow 1 7 u *
      (∑ j, Complex.exp (w j * ((T + v + u : ℝ) : ℂ))).re) := by
    simpa only [← Finset.mul_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hi.re
  have hmono : ∀ u : ℝ, upow 1 7 u * c ≤ upow 1 7 u *
      (∑ j, Complex.exp (w j * ((T + v + u : ℝ) : ℂ))).re := by
    intro u
    by_cases hu : upow 1 7 u = 0
    · simp only [hu, zero_mul, le_refl]
    have hs := support_upow_subset (by norm_num : (0 : ℝ) < 1) 7 hu
    have hu8 : |u| ≤ 8 := by
      norm_num at hs
      exact abs_le.mpr hs
    have hva : |v + u| ≤ R + 8 := (abs_add_le _ _).trans (add_le_add hv hu8)
    have hp := hpos (v + u) hva
    have hsum : (∑ j, Complex.exp (w j * ((T + v + u : ℝ) : ℂ))).re =
        Real.exp (x * (T + v + u)) *
          (∑ j, Complex.exp (((T + (v + u) : ℝ) : ℂ) * z j)).re := by
      have hterm (j : ι) : Complex.exp (w j * ((T + v + u : ℝ) : ℂ)) =
          (Real.exp (x * (T + v + u)) : ℂ) *
            Complex.exp (((T + (v + u) : ℝ) : ℂ) * z j) := by
        dsimp only [w]
        rw [add_mul, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul]
        congr 2
        push_cast
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum, Complex.re_ofReal_mul]
    rw [hsum]
    apply mul_le_mul_of_nonneg_left _ (upow_nonneg (by norm_num : (0 : ℝ) < 1) 7 u)
    have hexp : Real.exp (x * (T + v - 8)) ≤ Real.exp (x * (T + v + u)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hx
      have hulo := (abs_le.mp hu8).1
      linarith only [hulo]
    dsimp only [c]
    calc
      _ ≤ (3 / 4 : ℝ) * Real.exp (x * (T + v + u)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
  have hh := integral_mono ((integrable_upow 1 7).mul_const c) hir hmono
  rw [integral_mul_const, integral_upow (by norm_num : (0 : ℝ) < 1), one_mul] at hh
  rw [splineExponentialBlock_re_eq_integral]
  exact hh

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
