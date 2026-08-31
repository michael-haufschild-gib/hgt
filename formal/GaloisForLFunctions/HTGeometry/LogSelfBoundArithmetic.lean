import Mathlib
import GaloisForLFunctions.HTGeometry.LogBelowLinear

/-!
# The arithmetic of a logarithmic self-bound

Three real inequalities used to collapse `T ≤ A + 6 log(T+1) + B` into `T = O(A + B)`.

`log_le_two_mul_sqrt` (already in the corpus) makes the logarithmic term `O(√T)`, which drops
below `T/2` once `T` exceeds `1156`, and the self-bound then reads `T ≤ 2(A + B)`.

`log(1 + x^α) ≤ log 2 + α log⁺x` is the step that removes the `α`-power from the
logarithmic-derivative estimate, leaving a plain logarithm.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The collapse.**  A quantity bounded by `A + 6 log(T+1) + B` with `A + B` nonnegative is
bounded by `2(A+B) + 1156`: the logarithm is `O(√T)`, which is below `T/2` once `T` exceeds `1156`. -/
theorem le_of_le_add_six_log {T₀ A B : ℝ} (_hT0 : 0 ≤ T₀) (hAB : 0 ≤ A + B)
    (h : T₀ ≤ A + 6 * Real.log (T₀ + 1) + B) : T₀ ≤ 2 * (A + B) + 1156 := by
  rcases le_or_gt T₀ 1156 with hsmall | hbig
  · linarith
  · have hlog : Real.log (T₀ + 1) ≤ 2 * Real.sqrt (T₀ + 1) :=
      log_le_two_mul_sqrt (by linarith)
    have hsq : Real.sqrt (T₀ + 1) ^ 2 = T₀ + 1 := Real.sq_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt (T₀ + 1) := Real.sqrt_nonneg _
    have hkey : 24 * Real.sqrt (T₀ + 1) ≤ T₀ := by
      nlinarith [hsq, hs0, hbig]
    linarith

/-- **The `α`-power logarithm bound.**  `log(1 + x^α) ≤ log 2 + α·log⁺x`. -/
theorem log_one_add_rpow_le {x α : ℝ} (hx : 0 ≤ x) (hα : 0 < α) :
    Real.log (1 + x ^ α) ≤ Real.log 2 + α * Real.posLog x := by
  set m : ℝ := max 1 x with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm0 : (0 : ℝ) < m := by linarith
  have hxm : x ≤ m := le_max_right _ _
  have hpow : x ^ α ≤ m ^ α := Real.rpow_le_rpow hx hxm hα.le
  have hone : (1 : ℝ) ≤ m ^ α := Real.one_le_rpow hm1 hα.le
  have hsum : 1 + x ^ α ≤ 2 * m ^ α := by linarith
  have hlog : Real.log (1 + x ^ α) ≤ Real.log (2 * m ^ α) := by
    refine Real.log_le_log ?_ hsum
    have : (0 : ℝ) ≤ x ^ α := Real.rpow_nonneg hx _
    linarith
  have hval : Real.log (2 * m ^ α) = Real.log 2 + α * Real.log m := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hm0]
  have hposlog : Real.log m = Real.posLog x := by
    rcases le_or_gt x 1 with hle | hgt
    · have hmeq : m = 1 := by rw [hm]; exact max_eq_left hle
      rw [hmeq, Real.log_one]
      exact ((Real.posLog_eq_zero_iff x).mpr (by rw [abs_of_nonneg hx]; exact hle)).symm
    · have hmeq : m = x := by rw [hm]; exact max_eq_right hgt.le
      rw [hmeq]
      exact (Real.posLog_eq_log (by rw [abs_of_nonneg hx]; exact hgt.le)).symm
  rw [hval, hposlog] at hlog
  exact hlog

/-- **The self-bound collapse with an arbitrary logarithmic coefficient.**  Concavity of the
logarithm at the scale `4c` absorbs `c·log(T+1)` into `T/4` plus a constant. -/
theorem le_of_le_add_mul_log {T A c : ℝ} (hT : 0 ≤ T) (hc : 0 < c) (_hA : 0 ≤ A)
    (h : T ≤ A + c * Real.log (T + 1)) :
    T ≤ 2 * A + 2 * c * |Real.log (4 * c)| + 1 := by
  have hT1 : (0 : ℝ) < T + 1 := by linarith
  have h4c : (0 : ℝ) < 4 * c := by linarith
  have hkey : Real.log (T + 1) ≤ Real.log (4 * c) + (T + 1) / (4 * c) - 1 := by
    have hsub := Real.log_le_sub_one_of_pos (x := (T + 1) / (4 * c)) (by positivity)
    rw [Real.log_div (ne_of_gt hT1) (ne_of_gt h4c)] at hsub
    linarith
  have hmul : c * Real.log (T + 1) ≤ c * (Real.log (4 * c) + (T + 1) / (4 * c) - 1) :=
    mul_le_mul_of_nonneg_left hkey hc.le
  have hsimp : c * ((T + 1) / (4 * c)) = (T + 1) / 4 := by
    field_simp
  have habs : Real.log (4 * c) ≤ |Real.log (4 * c)| := le_abs_self _
  nlinarith [h, hmul, hsimp, habs, hc]

end GaloisForLFunctions.HTGeometry
