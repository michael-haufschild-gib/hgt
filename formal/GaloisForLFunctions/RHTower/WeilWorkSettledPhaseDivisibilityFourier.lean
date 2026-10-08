import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite cosine expansion of divisibility

Character orthogonality expresses an exact divisibility mask as an average of
rational cosine twists. This keeps the modulus fixed throughout the argument.
-/

open Complex Finset
noncomputable section
namespace RHTower.WeilSingularArithmetic

def divisibilityMask (Q n : ℕ) : ℝ := if Q ∣ n then 1 else 0

private theorem re_stdAddChar_nat_mul (Q : ℕ) [NeZero Q] (j : ZMod Q) (n : ℕ) :
    (ZMod.stdAddChar ((n : ZMod Q) * j)).re =
      Real.cos (2 * Real.pi * ((n : ℝ) * (j.val / Q))) := by
  have hc : (((n * j.val : ℕ) : ℤ) : ZMod Q) = (n : ZMod Q) * j := by simp
  rw [← hc, ZMod.stdAddChar_coe]
  have he : 2 * (Real.pi : ℂ) * I * ((n * j.val : ℕ) : ℤ) / (Q : ℂ) =
      ((2 * Real.pi * ((n : ℝ) * (j.val / Q)) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re]

theorem divisibilityMask_cosine_expansion (Q : ℕ) [NeZero Q] (n : ℕ) :
    divisibilityMask Q n =
      ∑ j : ZMod Q, (Q : ℝ)⁻¹ * Real.cos (2 * Real.pi * ((n : ℝ) * (j.val / Q))) := by
  have hc : ∑ j : ZMod Q, ZMod.stdAddChar ((n : ZMod Q) * j) =
      if Q ∣ n then (Q : ℂ) else 0 := by
    by_cases hn : Q ∣ n
    · have hz := (ZMod.natCast_eq_zero_iff n Q).mpr hn
      simp [hn, hz]
    · rw [if_neg hn]
      exact AddChar.sum_eq_zero_of_ne_one
        (ZMod.isPrimitive_stdAddChar Q (fun h => hn ((ZMod.natCast_eq_zero_iff n Q).mp h)))
  have hr := congrArg Complex.re hc
  simp only [Complex.re_sum, re_stdAddChar_nat_mul] at hr
  rw [← Finset.mul_sum, hr]
  have hQ : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
  by_cases hn : Q ∣ n <;> simp [divisibilityMask, hn, hQ]

end RHTower.WeilSingularArithmetic
