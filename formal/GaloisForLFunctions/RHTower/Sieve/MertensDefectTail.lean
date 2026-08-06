import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp

/-!
# The telescoping defect decays like `1/N`

The defect between one telescoping step of `logLog` and its discrete model is bounded by
`(log(i+1) − log i)·invLogVar i`, and the first factor is at most `1/i`.  Relaxing it to `1/2` — as
is enough for summability — throws away the whole decay: the tail of the defect series is
`1/(N·log N)`, not `1/(2 log N)`.
-/

namespace RHTower.Sieve

open Finset

/-- **The defect is `1/i` times the variation.** -/
theorem logLogDefect_le_div (i : ℕ) : logLogDefect i ≤ 1 / (i : ℝ) * invLogVar i := by
  unfold logLogDefect invLogVar
  split_ifs with h
  · have hiR : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
    have hi0 : (0 : ℝ) < (i : ℝ) := by linarith
    have hlogi : 0 < Real.log i := log_pos_of_two_le h
    have hlog1 : 0 < Real.log ((i : ℝ) + 1) := Real.log_pos (by linarith)
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have hstep : Real.log ((i : ℝ) + 1) - Real.log i ≤ 1 / (i : ℝ) := by
      have hdiv : Real.log (((i : ℝ) + 1) / (i : ℝ)) ≤ ((i : ℝ) + 1) / (i : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by linarith) (by linarith)] at hdiv
      have hval : ((i : ℝ) + 1) / (i : ℝ) - 1 = 1 / (i : ℝ) := by
        field_simp
        ring
      linarith [hdiv, hval.le, hval.ge]
    have hupper : logLog (i + 1) - logLog i
        ≤ (Real.log ((i : ℝ) + 1) - Real.log i) / Real.log i := by
      have hmono : Real.log i ≤ Real.log ((i : ℝ) + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      have := log_sub_log_le hlogi hmono
      simp only [logLog, hcast]
      exact this
    have hdiff : (Real.log ((i : ℝ) + 1) - Real.log i) / Real.log i
        - (Real.log ((i : ℝ) + 1) - Real.log i) / Real.log ((i : ℝ) + 1)
        = (Real.log ((i : ℝ) + 1) - Real.log i)
            * (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) := by
      field_simp
    have hvar : 0 ≤ 1 / Real.log i - 1 / Real.log ((i : ℝ) + 1) := inv_log_variation_nonneg h
    have hmul : (Real.log ((i : ℝ) + 1) - Real.log i)
        * (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1))
        ≤ 1 / (i : ℝ) * (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hstep hvar
    linarith [hupper, hdiff.le, hdiff.ge, hmul]
  · norm_num

/-- **The defect tail.**  It is `1/N` times the variation tail, hence `1/(N·log N)`. -/
theorem tsum_logLogDefect_add_le {N : ℕ} (hN : 2 ≤ N) :
    ∑' i, logLogDefect (i + N) ≤ 1 / (N : ℝ) * (1 / Real.log N) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hdshift : Summable (fun i => logLogDefect (i + N)) :=
    (summable_nat_add_iff N).2 summable_logLogDefect
  have hwshift : Summable (fun i => invLogVar (i + N)) :=
    (summable_nat_add_iff N).2 summable_invLogVar
  have hmajor : Summable (fun i => 1 / (N : ℝ) * invLogVar (i + N)) := hwshift.mul_left _
  have hterm : ∀ i : ℕ, logLogDefect (i + N) ≤ 1 / (N : ℝ) * invLogVar (i + N) := by
    intro i
    refine le_trans (logLogDefect_le_div (i + N)) ?_
    have hle : 1 / ((i : ℝ) + (N : ℝ)) ≤ 1 / (N : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hN0]
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have hcast : ((i + N : ℕ) : ℝ) = (i : ℝ) + (N : ℝ) := by push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_right hle (invLogVar_nonneg _)
  have hsum := Summable.tsum_mono hdshift hmajor hterm
  have htail : ∑' i, invLogVar (i + N) = 1 / Real.log N := tsum_invLogVar_add hN
  rw [tsum_mul_left, htail] at hsum
  exact hsum

end RHTower.Sieve
