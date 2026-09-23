import GaloisForLFunctions.RHTower.XiWardSchwarzCapSourcePairing

/-!
# Resonant quadrature of the literal Schwarz-paired Ward cap

At the moving cap resonance, the literal Schwarz-paired Cauchy kernel has
both a real and an imaginary component.  This module exposes the exact
quadrature of the actual completed-source density.  In particular, the real
source component has a strictly negative, nonzero resonant coefficient away
from height zero; an imaginary-source reserve alone cannot determine this
current.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact real coefficient of the literal Schwarz-paired cap kernel at its
moving Cauchy resonance. -/
theorem xiWardSchwarzCapDifference_resonant_re (s x : ℝ) :
    (xiWardSchwarzCapDifference x s x).re =
      -(8 * x ^ (2 : ℕ)) /
        ((51 / 100 + xiWardTransverseLevel s) *
          ((51 / 100 + xiWardTransverseLevel s) ^ (2 : ℕ) + 4 * x ^ (2 : ℕ))) := by
  let a : ℝ := 51 / 100 + xiWardTransverseLevel s
  have ha : 0 < a := by
    dsimp [a]
    have hlevel := xiWardTransverseLevel_mem_Ioo s
    linarith [hlevel.1]
  have ha0 : a ≠ 0 := ha.ne'
  have hsum0 : a ^ (2 : ℕ) + 4 * x ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_nonneg x, sq_pos_of_pos ha]
  rw [xiWardSchwarzCapDifference_resonant]
  have hprod :
      (((a : ℂ) + I * ((2 * x : ℝ) : ℂ)) * (a : ℂ)) =
        ((a ^ (2 : ℕ) : ℝ) : ℂ) + ((2 * a * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  change ((-4 * I * (x : ℂ)) *
      (((a : ℂ) + I * ((2 * x : ℝ) : ℂ)) * (a : ℂ))⁻¹).re =
    -(8 * x ^ (2 : ℕ)) / (a * (a ^ (2 : ℕ) + 4 * x ^ (2 : ℕ)))
  rw [hprod]
  rw [Complex.mul_re, Complex.inv_re, Complex.inv_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    sub_zero, zero_sub, add_zero, zero_add, mul_zero, zero_mul]
  rw [Complex.normSq_add_mul_I]
  norm_num
  field_simp [ha0, hsum0]
  ring

/-- Exact imaginary coefficient of the literal Schwarz-paired cap kernel at
its moving Cauchy resonance. -/
theorem xiWardSchwarzCapDifference_resonant_im (s x : ℝ) :
    (xiWardSchwarzCapDifference x s x).im =
      -(4 * x) /
        ((51 / 100 + xiWardTransverseLevel s) ^ (2 : ℕ) + 4 * x ^ (2 : ℕ)) := by
  let a : ℝ := 51 / 100 + xiWardTransverseLevel s
  rw [xiWardSchwarzCapDifference_resonant]
  have hprod :
      (((a : ℂ) + I * ((2 * x : ℝ) : ℂ)) * (a : ℂ)) =
        ((a ^ (2 : ℕ) : ℝ) : ℂ) + ((2 * a * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  change ((-4 * I * (x : ℂ)) *
      (((a : ℂ) + I * ((2 * x : ℝ) : ℂ)) * (a : ℂ))⁻¹).im =
    -(4 * x) / (a ^ (2 : ℕ) + 4 * x ^ (2 : ℕ))
  rw [hprod]
  rw [Complex.mul_im, Complex.inv_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    sub_zero, zero_sub, add_zero, zero_add, mul_zero, zero_mul]
  rw [Complex.normSq_add_mul_I]
  norm_num
  have ha : 0 < a := by
    dsimp [a]
    have hlevel := xiWardTransverseLevel_mem_Ioo s
    linarith [hlevel.1]
  have hsum0 : a ^ (2 : ℕ) + 4 * x ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_nonneg x, sq_pos_of_pos ha]
  field_simp [hsum0]
  ring

/-- The moving-resonance cap current is a fixed real quadrature of both
components of any complex source value. -/
theorem xiWardSchwarzCapDifference_resonant_mul_re
    (s x : ℝ) (z : ℂ) :
    (xiWardSchwarzCapDifference x s x * z).re =
      (-(8 * x ^ (2 : ℕ)) /
        ((51 / 100 + xiWardTransverseLevel s) *
          ((51 / 100 + xiWardTransverseLevel s) ^ (2 : ℕ) + 4 * x ^ (2 : ℕ)))) * z.re +
      ((4 * x) /
        ((51 / 100 + xiWardTransverseLevel s) ^ (2 : ℕ) + 4 * x ^ (2 : ℕ))) * z.im := by
  rw [Complex.mul_re, xiWardSchwarzCapDifference_resonant_re,
    xiWardSchwarzCapDifference_resonant_im]
  ring

/-- The literal completed prime--polar--Gamma cap density has the same exact
resonant quadrature.  This retains its source value unaltered. -/
theorem xiWardSchwarzCapFactorDensity_resonant_re (s x : ℝ) :
    (xiWardSchwarzCapDifference x s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re =
      (-(8 * x ^ (2 : ℕ)) /
        ((51 / 100 + xiWardTransverseLevel s) *
          ((51 / 100 + xiWardTransverseLevel s) ^ (2 : ℕ) + 4 * x ^ (2 : ℕ)))) *
        (continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re +
      ((4 * x) /
        ((51 / 100 + xiWardTransverseLevel s) ^ (2 : ℕ) + 4 * x ^ (2 : ℕ))) *
        (continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).im := by
  exact xiWardSchwarzCapDifference_resonant_mul_re s x
    (continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x))

/-- Unconditionally, the resonant real coefficient vanishes only at the
central height and is strictly negative at every other height. -/
theorem xiWardSchwarzCapDifference_resonant_re_zero_or_neg (s x : ℝ) :
    (xiWardSchwarzCapDifference x s x).re = 0 ∨
      (xiWardSchwarzCapDifference x s x).re < 0 := by
  by_cases hx : x = 0
  · left
    subst x
    rw [xiWardSchwarzCapDifference_resonant_re]
    norm_num
  · right
    rw [xiWardSchwarzCapDifference_resonant_re]
    have ha : 0 < 51 / 100 + xiWardTransverseLevel s := by
      have hlevel := xiWardTransverseLevel_mem_Ioo s
      linarith [hlevel.1]
    have hsum : 0 <
        (51 / 100 + xiWardTransverseLevel s) ^ (2 : ℕ) + 4 * x ^ (2 : ℕ) := by
      have hx2 : 0 < x ^ (2 : ℕ) := sq_pos_of_ne_zero hx
      nlinarith [sq_nonneg (51 / 100 + xiWardTransverseLevel s)]
    apply div_neg_of_neg_of_pos
    · have hx2 : 0 < x ^ (2 : ℕ) := sq_pos_of_ne_zero hx
      nlinarith
    · exact mul_pos ha hsum

end

end RHTower
