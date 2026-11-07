import GaloisForLFunctions.ThetaCuspSections.WeightedLegendreNorms

/-!
# Exterior control of every weighted Legendre mode

Differentiated Bonnet recurrence retains a nonpositive lower mode outside
the orthogonality interval. Dropping that term bounds each mode by its
leading monomial, with no degree lost to the endpoint weight.
-/

noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections

/-- Every shifted derivative is bounded by its exact leading monomial. -/
theorem shiftedLegendreDerivative_le_lead {x : ℝ} (hx : 1 ≤ x) (r n : ℕ) :
    (legendreDerivative (n + r) r).eval x ≤
      legendreDerivativeLead (n + r) r * x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp only [Nat.zero_add, pow_zero, mul_one, legendreDerivative_diagonal_eval, le_refl]
    · simpa only [Nat.zero_add, Nat.add_comm 1 r, pow_one] using
        (legendreDerivative_next_eval r x).le
    · have hprev := legendreDerivative_eval_nonneg hx (n + r) r
      have hcur := ih (n + 1) (by omega)
      have hb := legendreDerivative_bonnet (n + r) r x
      have hl := shiftedLegendreLead_succ r (n + 1)
      rw [show n + r + 2 = n + 2 + r by omega,
        show n + r + 1 = n + 1 + r by omega] at hb
      simp only [Nat.cast_add, Nat.cast_one] at hb hl
      have hpay := mul_le_mul_of_nonneg_left hcur
        (by positivity : 0 ≤ (2 * (n : ℝ) + 2 * r + 3) * x)
      have hdrop : 0 ≤ ((n : ℝ) + 2 * r + 1) *
          (legendreDerivative (n + r) r).eval x := by positivity
      apply (mul_le_mul_iff_right₀ (by positivity : 0 < (n : ℝ) + 2)).mp
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      nlinarith only [hb, hpay, hdrop,
        congrArg (fun z : ℝ => z * (x ^ (n + 1) * x)) hl]

theorem legendreDerivative_eval_neg_sq (n r : ℕ) (x : ℝ) :
    (legendreDerivative n r).eval (-x) ^ 2 = (legendreDerivative n r).eval x ^ 2 := by
  rw [legendreDerivative_neg, mul_pow, ← pow_mul, Nat.mul_comm (n + r) 2, pow_mul]
  norm_num

/-- The exact leading exterior bound holds on both sides, at every derivative order. -/
theorem shiftedLegendreDerivative_sq_le {x : ℝ} (hx : 1 ≤ |x|) (r n : ℕ) :
    (legendreDerivative (n + r) r).eval x ^ 2 ≤
      legendreDerivativeLead (n + r) r ^ 2 * |x| ^ (2 * n) := by
  have hh := pow_le_pow_left₀ (legendreDerivative_eval_nonneg hx (n + r) r)
    (shiftedLegendreDerivative_le_lead hx r n) 2
  rw [mul_pow, ← pow_mul, Nat.mul_comm n 2] at hh
  by_cases hx0 : 0 ≤ x
  · simpa only [abs_of_nonneg hx0] using hh
  · simpa only [abs_of_neg (lt_of_not_ge hx0), legendreDerivative_eval_neg_sq] using hh

#print axioms shiftedLegendreDerivative_le_lead
#print axioms shiftedLegendreDerivative_sq_le

end GaloisForLFunctions.ThetaCuspSections
