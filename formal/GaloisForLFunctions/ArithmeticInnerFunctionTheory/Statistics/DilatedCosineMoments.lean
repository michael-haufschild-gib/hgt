import GaloisForLFunctions.ArithmeticInnerFunctionTheory.Statistics.CharacterMoments

/-!
# Sato–Tate cosine coefficients and dilation

The Sato–Tate cosine coefficients vanish except at frequencies zero and two.
Consequently every positive Fourier mode of an integer dilation by at least
two has the uniform-law mean. Its second moment is exactly one half.
-/

open MeasureTheory
open GaloisForLFunctions.CompletedArithmeticForms (cosSum cosSum_eq_chebyshev)

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-- A cosine is the difference of two successive same-parity characters. -/
theorem cos_nat_add_two_eq_character_difference (n : ℕ) (θ : ℝ) :
    Real.cos (((n + 2 : ℕ) : ℝ) * θ) =
      (cosSum θ (n + 2) - cosSum θ n) / 2 := by
  have h := congrArg (Polynomial.eval (Real.cos θ))
    (Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ (n : ℤ))
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_sub,
    Polynomial.Chebyshev.T_real_cos] at h
  rw [cosSum_eq_chebyshev, cosSum_eq_chebyshev]
  push_cast at h ⊢
  linarith only [h]

theorem integrable_cos_nat (n : ℕ) :
    Integrable (fun θ => Real.cos ((n : ℝ) * θ)) satoTate := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun θ => ?_)
  exact Real.norm_cos_le_one _

/-- The only nonconstant Sato–Tate cosine coefficient is `-1/2` at frequency two. -/
theorem integral_satoTate_cos_nat (n : ℕ) :
    ∫ θ, Real.cos ((n : ℝ) * θ) ∂satoTate =
      if n = 0 then 1 else if n = 2 then -(1 / 2 : ℝ) else 0 := by
  rcases n with _ | _ | n
  · simp
  · have h := integral_cosSum 1
    simp_rw [cosSum_one] at h
    rw [integral_const_mul] at h
    norm_num only [Nat.cast_one, one_mul, Nat.reduceEqDiff, if_false] at h ⊢
    linarith only [h]
  · simp_rw [cos_nat_add_two_eq_character_difference]
    rw [integral_div, integral_sub]
    · simp only [integral_cosSum, Nat.add_eq_zero_iff, Nat.succ_ne_zero, and_false,
        if_false]
      by_cases hn : n = 0
      · subst n
        norm_num
      · rw [if_neg hn, if_neg (by omega : n + 2 ≠ 2)]
        ring
    · simpa only [pow_one] using integrable_cosSum_pow (n + 2) 1
    · simpa only [pow_one] using integrable_cosSum_pow n 1

/-- All positive Fourier modes of dilations by `a+2` have uniform-law mean. -/
theorem integral_satoTate_dilated_cos (a m : ℕ) :
    ∫ θ, Real.cos ((2 * (a + 2) * (m + 1) : ℕ) * θ) ∂satoTate = 0 := by
  rw [integral_satoTate_cos_nat, if_neg (by omega : 2 * (a + 2) * (m + 1) ≠ 0),
    if_neg (by nlinarith : 2 * (a + 2) * (m + 1) ≠ 2)]

/-- All frequencies at least two have raw second moment one half. -/
theorem integral_satoTate_cos_sq (n : ℕ) :
    ∫ θ, Real.cos (((n + 2 : ℕ) : ℝ) * θ) ^ 2 ∂satoTate = (1 / 2 : ℝ) := by
  have hpoint (θ : ℝ) : Real.cos (((n + 2 : ℕ) : ℝ) * θ) ^ 2 =
      (Real.cos (((2 * (n + 2) : ℕ) : ℝ) * θ) + 1) / 2 := by
    have h := Real.cos_two_mul (((n + 2 : ℕ) : ℝ) * θ)
    push_cast at h ⊢
    rw [show (2 * ((n : ℝ) + 2)) * θ = 2 * (((n : ℝ) + 2) * θ) by ring]
    linarith only [h]
  simp_rw [hpoint]
  rw [integral_div, integral_add (integrable_cos_nat _) (integrable_const 1),
    integral_satoTate_cos_nat]
  rw [if_neg (by omega : 2 * (n + 2) ≠ 0), if_neg (by omega : 2 * (n + 2) ≠ 2)]
  simp

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
