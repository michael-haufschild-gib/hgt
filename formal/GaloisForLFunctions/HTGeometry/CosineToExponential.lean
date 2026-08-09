import Mathlib

/-!
# A shifted cosine integral is dominated by its complex exponential

An oscillatory integral with a real cosine and a phase shift is the real part of a complex
exponential integral times a unimodular constant.  So any bound on the complex integral transfers
to the real one with no loss.

This is the bookkeeping that lets a two-branch exponential estimate be applied to a leading cosine
form, which is how Liouville–Green expansions are usually written.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- **The shifted cosine is the real part of a rotated exponential.** -/
theorem mul_cos_sub_eq_re {A φ θ : ℝ} :
    A * Real.cos (φ - θ)
      = (Complex.exp (-(θ : ℂ) * Complex.I)
          * ((A : ℂ) * Complex.exp (Complex.I * (φ : ℂ)))).re := by
  have hcomb : Complex.exp (-(θ : ℂ) * Complex.I)
      * ((A : ℂ) * Complex.exp (Complex.I * (φ : ℂ)))
      = (A : ℂ) * Complex.exp (((φ - θ : ℝ) : ℂ) * Complex.I) := by
    rw [mul_comm (Complex.I) ((φ : ℂ)), ← mul_assoc, mul_comm (Complex.exp _) ((A : ℂ)),
      mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hcomb, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **A shifted cosine integral is dominated by its complex exponential integral.** -/
theorem abs_integral_mul_cos_sub_le {a b θ : ℝ} {A φ : ℝ → ℝ}
    (hAc : ContinuousOn A (Set.uIcc a b)) (hφc : ContinuousOn φ (Set.uIcc a b)) :
    |∫ x in a..b, A x * Real.cos (φ x - θ)|
      ≤ ‖∫ x in a..b, (A x : ℂ) * Complex.exp (Complex.I * (φ x : ℂ))‖ := by
  have hint : IntervalIntegrable
      (fun x : ℝ => (A x : ℂ) * Complex.exp (Complex.I * (φ x : ℂ))) volume a b := by
    refine ((Complex.continuous_ofReal.comp_continuousOn hAc).mul ?_).intervalIntegrable
    refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn hφc
  have hrot : IntervalIntegrable
      (fun x : ℝ => Complex.exp (-(θ : ℂ) * Complex.I)
        * ((A x : ℂ) * Complex.exp (Complex.I * (φ x : ℂ)))) volume a b :=
    hint.const_mul _
  have hre := ContinuousLinearMap.intervalIntegral_comp_comm (Complex.reCLM) hrot
  rw [Complex.reCLM_apply] at hre
  have hcong : (∫ x in a..b, A x * Real.cos (φ x - θ))
      = ∫ x in a..b, Complex.reCLM (Complex.exp (-(θ : ℂ) * Complex.I)
          * ((A x : ℂ) * Complex.exp (Complex.I * (φ x : ℂ)))) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [Complex.reCLM_apply]
    exact mul_cos_sub_eq_re
  rw [hcong, hre, intervalIntegral.integral_const_mul]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul]
  have hunit : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
    rw [show (-(θ : ℂ)) = ((-θ : ℝ) : ℂ) by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hunit, one_mul]

end GaloisForLFunctions.HTGeometry
