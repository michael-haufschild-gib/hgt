import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TwoPrimeTowersSeeEveryOrdinateDifference

/-!
# Minus one and two prime logarithms

For integer coefficients, the principal logarithms of `-1`, `p`, and `q`
have polynomial separation. The imaginary part handles a nonzero
coefficient of `log(-1)`; the remaining case is effective Baker for two
prime logarithms. This form is distinct from an affine real combination
of `1`, `log p`, and `log q`.
-/

open Complex

noncomputable section
namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The imaginary component of the form is exactly the integer multiple of pi. -/
theorem minusOne_primeLog_im (p q : ℕ) (m a b : ℤ) :
    ((m : ℂ) * Complex.log (-1) +
      (((a : ℝ) * Real.log p + (b : ℝ) * Real.log q : ℝ) : ℂ)).im = (m : ℝ) * Real.pi := by
  rw [Complex.log_neg_one]
  simp

/-- Effective separation for the three principal logarithms `log(-1), log p, log q`. -/
theorem exists_minusOne_primeLog_separation {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m a b : ℤ, (m ≠ 0 ∨ a ≠ 0 ∨ b ≠ 0) →
      c * (2 + (|(m : ℝ)| + |(a : ℝ)| + |(b : ℝ)|)) ^ (-C) ≤
        ‖(m : ℂ) * Complex.log (-1) +
          (((a : ℝ) * Real.log p + (b : ℝ) * Real.log q : ℝ) : ℂ)‖ := by
  obtain ⟨c, C, hc, hC, hsep⟩ := exists_baker_separation hq hp hpq.symm
  refine ⟨min c Real.pi, C, lt_min hc Real.pi_pos, hC, fun m a b hnonzero => ?_⟩
  by_cases hm : m = 0
  · have hab : a ≠ 0 ∨ -b ≠ 0 := by
      rcases hnonzero with h | ha | hb
      · exact False.elim (h hm)
      · exact Or.inl ha
      · exact Or.inr (neg_ne_zero.mpr hb)
    have hb := hsep a (-b) hab
    have hmul := mul_le_mul_of_nonneg_right (min_le_left c Real.pi)
      (Real.rpow_nonneg (by positivity : 0 ≤ 2 + (|(a : ℝ)| + |(b : ℝ)|)) (-C))
    have hbound := hmul.trans (by
      simpa only [Int.cast_neg, abs_neg, neg_mul, sub_neg_eq_add] using hb)
    simpa only [hm, Int.cast_zero, abs_zero, zero_add, zero_mul,
      Complex.norm_real, Real.norm_eq_abs] using hbound
  · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    have hnorm := Complex.abs_im_le_norm ((m : ℂ) * Complex.log (-1) +
      (((a : ℝ) * Real.log p + (b : ℝ) * Real.log q : ℝ) : ℂ))
    rw [minusOne_primeLog_im, abs_mul, abs_of_pos Real.pi_pos] at hnorm
    have hpi : Real.pi ≤ ‖(m : ℂ) * Complex.log (-1) +
        (((a : ℝ) * Real.log p + (b : ℝ) * Real.log q : ℝ) : ℂ)‖ := by
      nlinarith only [hnorm, hm1, Real.pi_pos]
    have hpow : (2 + (|(m : ℝ)| + |(a : ℝ)| + |(b : ℝ)|)) ^ (-C) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by positivity) (neg_nonpos.mpr hC.le)
    calc min c Real.pi * (2 + (|(m : ℝ)| + |(a : ℝ)| + |(b : ℝ)|)) ^ (-C)
        ≤ min c Real.pi * 1 := mul_le_mul_of_nonneg_left hpow (le_min hc.le Real.pi_pos.le)
      _ ≤ Real.pi := by simpa only [mul_one] using min_le_right c Real.pi
      _ ≤ _ := hpi

#print axioms exists_minusOne_primeLog_separation

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
