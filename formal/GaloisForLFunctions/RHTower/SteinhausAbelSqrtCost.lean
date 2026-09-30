import GaloisForLFunctions.HTGeometry.RpowPartialSumBound
import GaloisForLFunctions.RHTower.BourgainPartialSummation

open scoped BigOperators

noncomputable section
namespace RHTower

/-- The square-root Abel cost is exactly the positive increment-weighted sum. -/
theorem steinhausAbelSqrtCost_eq (w : ℕ → ℝ) (N : ℕ) :
    w (N + 1) * Real.sqrt N +
      (∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) * Real.sqrt n) =
        ∑ n ∈ Finset.Icc 1 N, w n * (Real.sqrt n - Real.sqrt (n - 1 : ℕ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    linear_combination ih

/-- Each positive-index square-root increment is bounded by the reciprocal square root. -/
theorem steinhausSqrtIncrement_le (n : ℕ) (hn : 0 < n) :
    Real.sqrt n - Real.sqrt (n - 1 : ℕ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n 1 : ((n - 1 : ℕ) : ℝ) ≤ n)
  have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
    linarith
  have hmul : (Real.sqrt n - Real.sqrt (n - 1 : ℕ)) * Real.sqrt n ≤ 1 := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsqpred := Real.sq_sqrt (Nat.cast_nonneg (n - 1))
    have hp := mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg ((n - 1 : ℕ) : ℝ))
    nlinarith
  have h := (le_div_iff₀ (Real.sqrt_pos.2 hnR)).mpr hmul
  rw [Real.rpow_neg hnR.le, ← Real.sqrt_eq_rpow]
  simpa only [one_div] using h

/-- Every nonnegative weight below n^-beta has a uniform square-root Abel cost. -/
theorem steinhausAbelSqrtCost_le (w : ℕ → ℝ) {β : ℝ} (hβ : 0 < β) (hβhalf : β < 1 / 2)
    (hw : ∀ n, 1 ≤ n → 0 ≤ w n) (hbound : ∀ n, 1 ≤ n → w n ≤ (n : ℝ) ^ (-β))
    (N : ℕ) :
    w (N + 1) * Real.sqrt N +
      (∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) * Real.sqrt n) ≤
        (N : ℝ) ^ (1 / 2 - β) / (1 / 2 - β) := by
  rw [steinhausAbelSqrtCost_eq]
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      w n * (Real.sqrt n - Real.sqrt (n - 1 : ℕ)) ≤ (n : ℝ) ^ (-(β + 1 / 2)) := by
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    calc
      _ ≤ w n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (steinhausSqrtIncrement_le n hn1) (hw n hn1)
      _ ≤ (n : ℝ) ^ (-β) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (hbound n hn1) (Real.rpow_nonneg hnR.le _)
      _ = _ := by rw [← Real.rpow_add hnR]; congr 1; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have h := HTGeometry.sum_rpow_sub_one_le
    (by linarith : (0 : ℝ) < 1 / 2 - β) (by linarith : (1 / 2 : ℝ) - β < 1) N
  have hsum : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(β + 1 / 2))) =
      ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) - β - 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1 <;> ring
  rw [hsum]
  exact h

end RHTower
