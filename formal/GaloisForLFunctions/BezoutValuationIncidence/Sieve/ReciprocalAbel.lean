import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ProgressionCounts
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Reciprocal Abel summation from prefix bounds

Linear prefix growth gives a logarithmic interval-width bound for reciprocal
weights. Uniform signed prefix discrepancy transfers to arbitrary weights
through their endpoint and discrete variation.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.BezoutValuationIncidence


/-- Abel summation with inclusive prefix sums and the right endpoint retained. -/
theorem real_abel_Icc (f w : ℕ → ℝ) {A X : ℕ} (hAX : A ≤ X) :
    (∑ n ∈ Icc A X, f n * w n) =
      (∑ n ∈ Icc A X, f n) * w X +
        ∑ m ∈ Ico A X, (∑ n ∈ Icc A m, f n) * (w m - w (m + 1)) := by
  induction X, hAX using Nat.le_induction with
  | base => simp only [Icc_self, sum_singleton, Ico_self, sum_empty, add_zero]
  | succ X hAX ih =>
    have hsum (g : ℕ → ℝ) : (∑ n ∈ Icc A (X + 1), g n) =
        (∑ n ∈ Icc A X, g n) + g (X + 1) := by
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_succ_top (by omega : A ≤ X + 1),
        Ico_add_one_right_eq_Icc]
    rw [hsum, hsum, sum_Ico_succ_top hAX, ih]
    ring

/-- A linear upper bound for prefixes gives a reciprocal sum with logarithmic width. -/
theorem reciprocal_sum_of_linear_prefix {f : ℕ → ℝ} {D : ℝ}
    (hD : 0 ≤ D) {A X : ℕ} (hA : 1 ≤ A) (hAX : A ≤ X)
    (hprefix : ∀ m, A ≤ m → m ≤ X → (∑ n ∈ Icc A m, f n) ≤ D * (m : ℝ)) :
    (∑ n ∈ Icc A X, f n / (n : ℝ)) ≤
      D * (1 + Real.log X - Real.log A) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hX0 : (0 : ℝ) < X := hA0.trans_le (by exact_mod_cast hAX)
  have hidentity := real_abel_Icc f (fun n => 1 / (n : ℝ)) hAX
  simp only [mul_one_div] at hidentity
  rw [hidentity]
  have hend : (∑ n ∈ Icc A X, f n) / (X : ℝ) ≤ D := by
    apply (div_le_iff₀ hX0).mpr
    exact hprefix X hAX le_rfl
  have hterm (m : ℕ) (hm : m ∈ Ico A X) :
      (∑ n ∈ Icc A m, f n) * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) ≤
        D / ((m + 1 : ℕ) : ℝ) := by
    have hmA := (mem_Ico.mp hm).1
    have hm0 : (0 : ℝ) < m := hA0.trans_le (by exact_mod_cast hmA)
    have hnext : (m : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.le_succ m
    have hnn : 0 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le hm0 hnext)
    refine (mul_le_mul_of_nonneg_right (hprefix m hmA (mem_Ico.mp hm).2.le) hnn).trans_eq ?_
    push_cast
    field_simp [hm0.ne']
    ring
  have hlog : (∑ m ∈ Ico A X, 1 / ((m + 1 : ℕ) : ℝ)) ≤
      Real.log X - Real.log A := by
    have hpoint (m : ℕ) (hm : m ∈ Ico A X) :
        1 / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log m := by
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hA.trans (mem_Ico.mp hm).1
      have hmnext : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have h := Real.log_le_sub_one_of_pos (div_pos hm0 hmnext)
      rw [Real.log_div hm0.ne' hmnext.ne'] at h
      have he : (m : ℝ) / (m + 1 : ℕ) - 1 = -(1 / (m + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      rw [he] at h
      linarith only [h]
    refine (sum_le_sum hpoint).trans_eq ?_
    rw [sum_Ico_eq_sub _ hAX, sum_range_sub (fun n : ℕ => Real.log (n : ℝ)) X,
      sum_range_sub (fun n : ℕ => Real.log (n : ℝ)) A]
    ring
  have htail : (∑ m ∈ Ico A X,
      (∑ n ∈ Icc A m, f n) * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ))) ≤
      D * (Real.log X - Real.log A) := by
    refine (sum_le_sum hterm).trans ?_
    rw [show (∑ m ∈ Ico A X, D / ((m + 1 : ℕ) : ℝ)) =
      D * ∑ m ∈ Ico A X, 1 / ((m + 1 : ℕ) : ℝ) by simp only [mul_sum, mul_one_div]]
    exact mul_le_mul_of_nonneg_left hlog hD
  linarith only [hend, htail]

#print axioms reciprocal_sum_of_linear_prefix

/-- A uniform prefix discrepancy transfers to weights through endpoint and variation. -/
theorem abs_weighted_sum_le_of_prefix {f w : ℕ → ℝ} {C : ℝ}
    {A X : ℕ} (hAX : A ≤ X)
    (hprefix : ∀ m, A ≤ m → m ≤ X → |∑ n ∈ Icc A m, f n| ≤ C) :
    |∑ n ∈ Icc A X, f n * w n| ≤
      C * (|w X| + ∑ m ∈ Ico A X, |w (m + 1) - w m|) := by
  rw [real_abel_Icc f w hAX]
  refine (abs_add_le _ _).trans ?_
  have hend : |(∑ n ∈ Icc A X, f n) * w X| ≤ C * |w X| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hprefix X hAX le_rfl) (abs_nonneg _)
  have htail : |∑ m ∈ Ico A X,
      (∑ n ∈ Icc A m, f n) * (w m - w (m + 1))| ≤
      C * ∑ m ∈ Ico A X, |w (m + 1) - w m| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    rw [abs_mul, abs_sub_comm (w m)]
    exact mul_le_mul_of_nonneg_right
      (hprefix m (mem_Ico.mp hm).1 (mem_Ico.mp hm).2.le) (abs_nonneg _)
  exact (add_le_add hend htail).trans_eq (mul_add _ _ _).symm

#print axioms abs_weighted_sum_le_of_prefix

end GaloisForLFunctions.BezoutValuationIncidence
