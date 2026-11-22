import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Simple zeros of the binary scale denominator

A radix with logarithmic energy ℓ has dilation energy 2ℓ. After centering
at inverse temperature one half, the return frequencies are πk/ℓ.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation

/-- The geometric renewal factor with the energy of the squared radix. -/
def scaleFactor (l : ℝ) (s : ℂ) := 1-Complex.exp (-(s-((1/2:ℝ):ℂ))*(2*(l:ℂ)))

/-- Physical inverse temperature with the k-th clock return. -/
def clockPoint (l : ℝ) (k : ℤ) : ℂ := ⟨1/2,(k:ℝ)*(Real.pi/l)⟩

private theorem exponent_at_clock (l : {r : ℝ // 0 < r}) (k : ℤ) :
    -(clockPoint l.val k-((1/2:ℝ):ℂ))*(2*(l.val:ℂ)) = ((-k:ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
  have he : clockPoint l.val k = ((1/2:ℝ):ℂ)+((((k:ℝ)*(Real.pi/l.val)):ℝ):ℂ)*Complex.I := by
    apply Complex.ext <;> simp [clockPoint]
  rw [he,add_sub_cancel_left,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_intCast,Int.cast_neg]
  field_simp [Complex.ofReal_ne_zero.mpr l.property.ne']

theorem scaleFactor_zero_iff (l : {r : ℝ // 0 < r}) (s : ℂ) :
    scaleFactor l.val s = 0 ↔ ∃ k : ℤ, s = clockPoint l.val k := by
  rw [scaleFactor,sub_eq_zero,eq_comm,Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨-k,?_⟩
    have h := exponent_at_clock l (-k)
    simp only [neg_neg] at h
    have hL : 2*(l.val:ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr l.property.ne')
    have he := mul_right_cancel₀ hL (hk.trans h.symm)
    linear_combination -he
  · rintro ⟨k,rfl⟩
    exact ⟨-k,exponent_at_clock l k⟩

theorem scaleFactor_analytic (l : ℝ) (s : ℂ) : AnalyticAt ℂ (scaleFactor l) s :=
  analyticAt_const.sub (((analyticAt_id.sub analyticAt_const).neg.mul analyticAt_const).cexp)

theorem scaleFactor_derivative (l : {r : ℝ // 0 < r}) (k : ℤ) :
    HasDerivAt (scaleFactor l.val) (2*(l.val:ℂ)) (clockPoint l.val k) := by
  let w := clockPoint l.val k
  have he := (scaleFactor_zero_iff l w).mpr ⟨k,rfl⟩
  change 1-Complex.exp (-(w-((1/2:ℝ):ℂ))*(2*(l.val:ℂ))) = 0 at he
  have h := ((((hasDerivAt_id w).sub_const ((1/2:ℝ):ℂ)).neg.mul_const (2*(l.val:ℂ))).cexp).const_sub 1
  change HasDerivAt (scaleFactor l.val) (-(Complex.exp (-(w-((1/2:ℝ):ℂ))*(2*(l.val:ℂ)))*(-1*(2*(l.val:ℂ))))) w at h
  simpa only [(sub_eq_zero.mp he).symm,one_mul,neg_one_mul,neg_neg] using h

#print axioms scaleFactor_zero_iff
#print axioms scaleFactor_analytic
#print axioms scaleFactor_derivative

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation
