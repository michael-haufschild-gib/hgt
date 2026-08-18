import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp

/-!
# The exponential of a Mertens difference

The sieve saving is `exp(mertensS h − mertensS P₁)^{-2}`, so the quantitative form of Mertens'
second theorem has to be converted into a bound on that exponential.  Over a range of primes the
difference of the two Mertens sums is `log(log h / log P₁)` up to the two error terms, so the
exponential is the ratio `log h / log P₁` up to an explicit constant factor.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The explicit error of Mertens' second theorem at a cutoff. -/
def mertensErr (N : ℕ) : ℝ := (2 * mertensFirstConst + 1 / 2) / Real.log N

/-- **The exponential of a Mertens difference is the ratio of the logarithms.** -/
theorem exp_mertens_diff_ge {P₁ h : ℕ} (hP₁ : 2 ≤ P₁) (hh : 2 ≤ h) :
    (Real.log h / Real.log P₁) * Real.exp (-(mertensErr P₁ + mertensErr h))
      ≤ Real.exp (mertensS h - mertensS P₁) := by
  have hlP : 0 < Real.log (P₁ : ℝ) := log_pos_of_two_le hP₁
  have hlh : 0 < Real.log (h : ℝ) := log_pos_of_two_le hh
  have hP := abs_mertensS_sub_logLog_sub_const_le hP₁
  have hH := abs_mertensS_sub_logLog_sub_const_le hh
  rw [abs_le] at hP hH
  have hlow : Real.log (Real.log (h : ℝ)) - Real.log (Real.log (P₁ : ℝ))
      - (mertensErr P₁ + mertensErr h)
      ≤ mertensS h - mertensS P₁ := by
    rw [mertensErr, mertensErr]
    have h1 := hH.1
    have h2 := hP.2
    simp only [logLog] at h1 h2
    linarith
  have hstep : Real.exp (Real.log (Real.log (h : ℝ)) - Real.log (Real.log (P₁ : ℝ))
      - (mertensErr P₁ + mertensErr h))
      ≤ Real.exp (mertensS h - mertensS P₁) := Real.exp_le_exp.2 hlow
  refine le_trans (le_of_eq ?_) hstep
  rw [show Real.log (Real.log (h : ℝ)) - Real.log (Real.log (P₁ : ℝ))
      - (mertensErr P₁ + mertensErr h)
      = (Real.log (Real.log (h : ℝ)) - Real.log (Real.log (P₁ : ℝ)))
        + (-(mertensErr P₁ + mertensErr h)) from by ring,
    Real.exp_add, Real.exp_sub, Real.exp_log hlh, Real.exp_log hlP]

end

end RHTower.Sieve
