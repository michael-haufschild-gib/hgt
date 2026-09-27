import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Whole-amplitude perturbation bounds in the sampled energy norm -/

namespace GaloisForLFunctions

private theorem weighted_complex_young (a b : ℂ) (η : {η : ℝ // 0 < η}) :
    2 * ‖a‖ * ‖b‖ ≤ (η : ℝ) * ‖a‖ ^ 2 + (1 / (η : ℝ)) * ‖b‖ ^ 2 := by
  apply (mul_le_mul_iff_right₀ η.property).mp
  have hi : (1 / (η : ℝ)) * (η : ℝ) = 1 := one_div_mul_cancel η.property.ne'
  nlinarith [sq_nonneg ((η : ℝ) * ‖a‖ - ‖b‖)]

/-- The complex square retains its complete mixed term. -/
theorem norm_complex_square_add_sub_le (a b : ℂ) (η : {η : ℝ // 0 < η}) :
    ‖(a + b) ^ 2 - a ^ 2‖ ≤
      (η : ℝ) * ‖a‖ ^ 2 + (1 + 1 / (η : ℝ)) * ‖b‖ ^ 2 := by
  have hbound : ‖(a + b) ^ 2 - a ^ 2‖ ≤ 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by
    calc
      _ = ‖(a * b + a * b) + b ^ 2‖ := by congr 1; ring
      _ ≤ (‖a * b‖ + ‖a * b‖) + ‖b ^ 2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by rw [norm_mul, norm_pow]; ring
  nlinarith [weighted_complex_young a b η]

/-- The corresponding norm-square perturbation has the same degree-free bound. -/
theorem abs_complex_norm_square_add_sub_le (a b : ℂ) (η : {η : ℝ // 0 < η}) :
    |‖a + b‖ ^ 2 - ‖a‖ ^ 2| ≤
      (η : ℝ) * ‖a‖ ^ 2 + (1 + 1 / (η : ℝ)) * ‖b‖ ^ 2 := by
  have hdiff : |‖a + b‖ - ‖a‖| ≤ ‖b‖ := by
    simpa only [add_sub_cancel_left] using abs_norm_sub_norm_le (a + b) a
  have hsum : ‖a + b‖ + ‖a‖ ≤ 2 * ‖a‖ + ‖b‖ := by
    linarith [norm_add_le a b]
  have hbound : |‖a + b‖ ^ 2 - ‖a‖ ^ 2| ≤ 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by
    calc
      _ = |‖a + b‖ - ‖a‖| * (‖a + b‖ + ‖a‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        ring
      _ ≤ ‖b‖ * (2 * ‖a‖ + ‖b‖) :=
        mul_le_mul hdiff hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  nlinarith [weighted_complex_young a b η]

end GaloisForLFunctions
