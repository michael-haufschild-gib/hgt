import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A uniform lower bound on short clock chords -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- This step stays inside one reciprocal occupation gap and one quarter of a clock cycle. -/
def shortStep : ℝ := min (1/4:ℝ) (Real.pi/2)

theorem shortStep_pos : 0 < shortStep := lt_min (by norm_num) (half_pos Real.pi_pos)

def shortChordFactor (σ : ℝ) : ℝ := Real.exp (-(shortStep*σ))*(2/Real.pi)*shortStep

theorem shortChordFactor_pos (σ : ℝ) : 0 < shortChordFactor σ :=
  mul_pos (mul_pos (Real.exp_pos _) (div_pos (by norm_num) Real.pi_pos)) shortStep_pos

/-- The imaginary component dominates the sine chord on the positive quarter turn. -/
private theorem damped_sine {σ t v : ℝ} (hθ : 0 ≤ v*t) (hquarter : v*t ≤ Real.pi/2) :
    Real.exp (-(v*σ))*((2/Real.pi)*(v*t)) ≤ ‖1-((Real.exp (-v):ℝ):ℂ)^(⟨σ,t⟩:ℂ)‖ := by
  let z : ℂ := ⟨σ,t⟩
  have hi : (1-((Real.exp (-v):ℝ):ℂ)^z).im = Real.exp (-(v*σ))*Real.sin (v*t) := by
    rw [Complex.sub_im,Complex.one_im,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp,Complex.exp_im,Complex.mul_re,Complex.mul_im]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,zero_sub,neg_mul,Real.sin_neg,mul_neg,neg_neg,z]
  have hn := (le_abs_self _).trans (Complex.abs_im_le_norm (1-((Real.exp (-v):ℝ):ℂ)^z))
  rw [hi] at hn
  exact (mul_le_mul_of_nonneg_left (Real.mul_le_sin hθ hquarter) (Real.exp_pos _).le).trans hn

/-- An attenuation of logarithmic size d/R retains a fixed fraction of t/R in its chord length all the way down to angle zero. -/
theorem short_chord_lower {σ t R : ℝ} (hσ : 0 ≤ σ) (ht : 0 ≤ t) (hR : 1 ≤ R) (htR : t ≤ R) :
    shortChordFactor σ*(t/R) ≤ ‖1-((Real.exp (-(shortStep/R)):ℝ):ℂ)^(⟨σ,t⟩:ℂ)‖ := by
  let v := shortStep/R
  have hRp := zero_lt_one.trans_le hR
  have hv : 0 < v := div_pos shortStep_pos hRp
  have hvle : v ≤ shortStep := div_le_self shortStep_pos.le hR
  have ha : v*t ≤ Real.pi/2 := (mul_le_mul_of_nonneg_left htR hv.le).trans
    ((div_mul_cancel₀ shortStep hRp.ne').trans_le (min_le_right _ _))
  have hθ := mul_nonneg hv.le ht
  have he := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hvle hσ))
  have hmul := mul_le_mul_of_nonneg_right he (mul_nonneg (div_pos (by norm_num : (0:ℝ)<2) Real.pi_pos).le hθ)
  have hb := (hmul.trans (damped_sine (σ := σ) hθ ha))
  exact (show shortChordFactor σ*(t/R) = Real.exp (-(shortStep*σ))*((2/Real.pi)*(v*t)) by dsimp only [shortChordFactor,v]; ring).trans_le hb

theorem short_retention_loss {R : ℝ} : 1-Real.exp (-(shortStep/R)) ≤ shortStep/R := by
  linarith only [Real.add_one_le_exp (-(shortStep/R))]

#print axioms short_chord_lower

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
