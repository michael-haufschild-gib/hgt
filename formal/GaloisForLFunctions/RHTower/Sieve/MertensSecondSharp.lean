import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# The variation series of `1/log`

The discrete proof of Mertens' second theorem controls two remainder series by the total variation

`∑_{2 ≤ i < N} (1/log i − 1/log(i+1)) = 1/log 2 − 1/log N`.

Bounding that variation by its value at `N = ∞` costs a fixed additive constant.  Keeping it as a
convergent series instead costs only its *tail*, which is `1/log N` and decays.

This module establishes the series: nonnegativity, the partial sums, summability, and the exact
tail.  It is the mechanism by which every additive constant below becomes a decaying error.
-/

namespace RHTower.Sieve

open Finset

/-- The variation of `1/log` across one step, extended by zero below `2`. -/
noncomputable def invLogVar (i : ℕ) : ℝ :=
  if 2 ≤ i then 1 / Real.log i - 1 / Real.log ((i : ℝ) + 1) else 0

theorem invLogVar_nonneg (i : ℕ) : 0 ≤ invLogVar i := by
  unfold invLogVar
  split_ifs with h
  · exact inv_log_variation_nonneg h
  · exact le_rfl

/-- The partial sums of the variation series. -/
theorem sum_range_invLogVar {N : ℕ} (hN : 2 ≤ N) :
    ∑ i ∈ Finset.range N, invLogVar i = 1 / Real.log 2 - 1 / Real.log N := by
  classical
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) hN]
  have hlow : ∑ i ∈ Finset.Ico 0 2, invLogVar i = 0 := by
    rw [Finset.sum_eq_zero]
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold invLogVar
    rw [if_neg (by omega)]
  have hhigh : ∑ i ∈ Finset.Ico 2 N, invLogVar i
      = ∑ i ∈ Finset.Ico 2 N, (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold invLogVar
    rw [if_pos hi.1]
  rw [hlow, hhigh, sum_Ico_inv_log_variation hN, zero_add]

/-- The variation series converges. -/
theorem summable_invLogVar : Summable invLogVar := by
  refine summable_of_sum_range_le (c := 1 / Real.log 2) invLogVar_nonneg ?_
  intro n
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp
      positivity
    · simp [invLogVar]
      positivity
  · rw [sum_range_invLogVar hn]
    have hlogn : 0 < Real.log n := log_pos_of_two_le hn
    have : 0 < 1 / Real.log n := by positivity
    linarith

/-- **The tail of the variation series.**  It is exactly `1/log N`, and so decays. -/
theorem tsum_invLogVar_add {N : ℕ} (hN : 2 ≤ N) :
    ∑' i, invLogVar (i + N) = 1 / Real.log N := by
  have hsplit := summable_invLogVar.sum_add_tsum_nat_add N
  have htot : ∑' i, invLogVar i = 1 / Real.log 2 := by
    refine tendsto_nhds_unique summable_invLogVar.hasSum.tendsto_sum_nat ?_
    have hlog : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hinv : Filter.Tendsto (fun n : ℕ => 1 / Real.log n) Filter.atTop (nhds 0) := by
      refine hlog.inv_tendsto_atTop.congr ?_
      intro n
      rw [Pi.inv_apply, one_div]
    have hlim : Filter.Tendsto (fun n : ℕ => 1 / Real.log 2 - 1 / Real.log n) Filter.atTop
        (nhds (1 / Real.log 2)) := by
      have hsub := (tendsto_const_nhds (α := ℕ) (x := 1 / Real.log 2)
        (f := Filter.atTop)).sub hinv
      simpa using hsub
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact (sum_range_invLogVar hn).symm
  rw [htot, sum_range_invLogVar hN] at hsplit
  linarith

/-- The remainder weight of the summation by parts, extended by zero below `2`. -/
noncomputable def mertensRemTerm (i : ℕ) : ℝ := invLogVar i * (mertensA i - Real.log i)

theorem abs_mertensRemTerm_le (i : ℕ) :
    |mertensRemTerm i| ≤ mertensFirstConst * invLogVar i := by
  unfold mertensRemTerm invLogVar
  split_ifs with h
  · rw [abs_mul, abs_of_nonneg (inv_log_variation_nonneg h), mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_mertensA_sub_log_le (by omega)) (inv_log_variation_nonneg h)
  · simp

theorem summable_mertensRemTerm : Summable mertensRemTerm := by
  refine Summable.of_norm_bounded (summable_invLogVar.mul_left mertensFirstConst) ?_
  intro i
  rw [Real.norm_eq_abs]
  exact abs_mertensRemTerm_le i

/-- The gap between one telescoping step of `logLog` and its discrete model. -/
noncomputable def logLogDefect (i : ℕ) : ℝ :=
  if 2 ≤ i then
    (logLog (i + 1) - logLog i) - (Real.log ((i : ℝ) + 1) - Real.log i) / Real.log ((i : ℝ) + 1)
  else 0

theorem logLogDefect_nonneg (i : ℕ) : 0 ≤ logLogDefect i := by
  unfold logLogDefect
  split_ifs with h
  · have hlogi : 0 < Real.log i := log_pos_of_two_le h
    have hmono : Real.log i ≤ Real.log ((i : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have hle := le_log_sub_log hlogi hmono
    simp only [logLog, hcast]
    linarith
  · exact le_rfl

theorem logLogDefect_le (i : ℕ) : logLogDefect i ≤ (1 / 2) * invLogVar i := by
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
    have hsmall : Real.log ((i : ℝ) + 1) - Real.log i ≤ 1 / 2 := by
      have : 1 / (i : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hi0 (by norm_num)]
        linarith
      linarith
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
        ≤ (1 / 2) * (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hsmall hvar
    linarith [hupper, hdiff.le, hdiff.ge, hmul]
  · norm_num

theorem summable_logLogDefect : Summable logLogDefect := by
  refine Summable.of_nonneg_of_le logLogDefect_nonneg logLogDefect_le ?_
  exact summable_invLogVar.mul_left (1 / 2)

/-- The discrete model differs from the telescoped iterated logarithm by the defect series. -/
theorem logLogIncrementSum_eq {N : ℕ} (hN : 2 ≤ N) :
    logLogIncrementSum N
      = logLog N - logLog 2 - ∑ i ∈ Finset.range N, logLogDefect i := by
  classical
  have hlow : ∑ i ∈ Finset.Ico 0 2, logLogDefect i = 0 := by
    rw [Finset.sum_eq_zero]
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold logLogDefect
    rw [if_neg (by omega)]
  have hrange : ∑ i ∈ Finset.range N, logLogDefect i
      = ∑ i ∈ Finset.Ico 2 N, logLogDefect i := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) hN, hlow, zero_add]
  have hterm : ∑ i ∈ Finset.Ico 2 N, logLogDefect i
      = ∑ i ∈ Finset.Ico 2 N, ((logLog (i + 1) - logLog i)
          - (Real.log ((i : ℝ) + 1) - Real.log i) / Real.log ((i : ℝ) + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold logLogDefect
    rw [if_pos hi.1]
  rw [hrange, hterm, Finset.sum_sub_distrib, sum_Ico_telescope logLog hN]
  unfold logLogIncrementSum
  ring

theorem sum_range_mertensRemTerm {N : ℕ} (hN : 2 ≤ N) :
    ∑ i ∈ Finset.range N, mertensRemTerm i
      = ∑ i ∈ Finset.Ico 2 N,
          (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * (mertensA i - Real.log i) := by
  classical
  have hlow : ∑ i ∈ Finset.Ico 0 2, mertensRemTerm i = 0 := by
    rw [Finset.sum_eq_zero]
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold mertensRemTerm invLogVar
    rw [if_neg (by omega), zero_mul]
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) hN, hlow, zero_add]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.mem_Ico] at hi
  unfold mertensRemTerm invLogVar
  rw [if_pos hi.1]

/-- **The decomposition behind the sharp form.**  Every additive constant of the classical proof is
here a partial sum of a convergent series. -/
theorem mertensS_decomposition {N : ℕ} (hN : 2 ≤ N) :
    mertensS N = 1 + (mertensA N - Real.log N) / Real.log N
      + (logLog N - logLog 2 - ∑ i ∈ Finset.range N, logLogDefect i)
      + ∑ i ∈ Finset.range N, mertensRemTerm i := by
  have hlogN : 0 < Real.log N := log_pos_of_two_le hN
  have hsplit : ∑ i ∈ Finset.Ico 2 N,
      (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * mertensA i
        = logLogIncrementSum N
          + ∑ i ∈ Finset.Ico 2 N,
              (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * (mertensA i - Real.log i) := by
    rw [← sum_Ico_variation_mul_log N, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have habel := mertensS_eq_abel N
  rw [hsplit, logLogIncrementSum_eq hN, ← sum_range_mertensRemTerm hN] at habel
  have hfrac : mertensA N / Real.log N = 1 + (mertensA N - Real.log N) / Real.log N := by
    field_simp
    ring
  rw [habel, hfrac]
  ring

/-- The Meissel–Mertens constant, as the limit of the two remainder series. -/
noncomputable def meisselMertensConst : ℝ :=
  1 - logLog 2 - ∑' i, logLogDefect i + ∑' i, mertensRemTerm i

/-- **Mertens' second theorem with a decaying error.**  The error is `O(1/log N)`, not a fixed
additive constant, so window differences telescope instead of accumulating. -/
theorem abs_mertensS_sub_logLog_sub_const_le {N : ℕ} (hN : 2 ≤ N) :
    |mertensS N - logLog N - meisselMertensConst|
      ≤ (2 * mertensFirstConst + 1 / 2) / Real.log N := by
  have hlogN : 0 < Real.log N := log_pos_of_two_le hN
  have hd := summable_logLogDefect.sum_add_tsum_nat_add N
  have hv := summable_mertensRemTerm.sum_add_tsum_nat_add N
  have hdshift : Summable (fun i => logLogDefect (i + N)) :=
    (summable_nat_add_iff N).2 summable_logLogDefect
  have hvshift : Summable (fun i => mertensRemTerm (i + N)) :=
    (summable_nat_add_iff N).2 summable_mertensRemTerm
  have hwshift : Summable (fun i => invLogVar (i + N)) :=
    (summable_nat_add_iff N).2 summable_invLogVar
  -- the error term of the summation by parts
  have herr : |(mertensA N - Real.log N) / Real.log N| ≤ mertensFirstConst / Real.log N := by
    rw [abs_div, abs_of_pos hlogN]
    exact div_le_div_of_nonneg_right (abs_mertensA_sub_log_le (by omega)) hlogN.le
  -- the defect tail
  have hdtail : ∑' i, logLogDefect (i + N) ≤ (1 / 2) / Real.log N := by
    have hle : ∑' i, logLogDefect (i + N) ≤ ∑' i, (1 / 2) * invLogVar (i + N) :=
      Summable.tsum_le_tsum (fun i => logLogDefect_le _) hdshift (hwshift.mul_left (1 / 2))
    rw [tsum_mul_left, tsum_invLogVar_add hN] at hle
    calc ∑' i, logLogDefect (i + N) ≤ (1 / 2) * (1 / Real.log N) := hle
      _ = (1 / 2) / Real.log N := by ring
  have hdnonneg : 0 ≤ ∑' i, logLogDefect (i + N) :=
    tsum_nonneg (fun i => logLogDefect_nonneg _)
  -- the remainder tail
  have hvtail : |∑' i, mertensRemTerm (i + N)| ≤ mertensFirstConst / Real.log N := by
    have hnorm : Summable (fun i => ‖mertensRemTerm (i + N)‖) := by
      refine Summable.of_nonneg_of_le (fun i => norm_nonneg _)
        (fun i => abs_mertensRemTerm_le (i + N)) ?_
      exact hwshift.mul_left mertensFirstConst
    have hle : ∑' i, ‖mertensRemTerm (i + N)‖
        ≤ ∑' i, mertensFirstConst * invLogVar (i + N) :=
      Summable.tsum_le_tsum (fun i => abs_mertensRemTerm_le _) hnorm
        (hwshift.mul_left mertensFirstConst)
    rw [tsum_mul_left, tsum_invLogVar_add hN] at hle
    refine le_trans (norm_tsum_le_tsum_norm hnorm) ?_
    calc ∑' i, ‖mertensRemTerm (i + N)‖ ≤ mertensFirstConst * (1 / Real.log N) := hle
      _ = mertensFirstConst / Real.log N := by ring
  have hdecomp := mertensS_decomposition hN
  have hkey : mertensS N - logLog N - meisselMertensConst
      = (mertensA N - Real.log N) / Real.log N
        + (∑' i, logLogDefect (i + N)) - (∑' i, mertensRemTerm (i + N)) := by
    unfold meisselMertensConst
    rw [hdecomp]
    linarith [hd, hv]
  rw [hkey]
  have h1 := abs_le.1 herr
  have h2 := abs_le.1 hvtail
  have hsplit2 : (2 * mertensFirstConst + 1 / 2) / Real.log N
      = 2 * (mertensFirstConst / Real.log N) + (1 / 2) / Real.log N := by ring
  rw [abs_le, hsplit2]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hdtail, hdnonneg]

end RHTower.Sieve
