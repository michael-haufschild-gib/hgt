import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer
import GaloisForLFunctions.RHTower.ZetaNotchRampMainTerm
import GaloisForLFunctions.RHTower.BaezDuarteLogDualEnergy
import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothCancellation

/-!
# The logarithmic moment of a growing prime head

Abel summation transfers the exact Mertens constant to the logarithmically
weighted prime head. The leading term is half the logarithm squared; its
remaining error is smaller than one logarithm.
-/

open Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory
noncomputable section

private def primeHeadLogStep (n : ℕ) : ℝ := Real.log (n + 1 : ℕ) - Real.log n

private theorem logStep_nonneg (n : ℕ) : 0 ≤ primeHeadLogStep n :=
  _root_.RHTower.WeilAbscissa.log_step_nonneg n

private theorem logStep_le_inv {n : ℕ} (hn : 0 < n) : primeHeadLogStep n ≤ 1 / (n : ℝ) :=
  _root_.RHTower.log_natSucc_sub_log_le_inv hn

private theorem range_succ_eq_Icc_of_zero (f : ℕ → ℝ) (hf : f 0 = 0) (N : ℕ) :
    (∑ n ∈ range (N + 1), f n) = ∑ n ∈ Icc 1 N, f n := by
  have hset : range (N + 1) = insert 0 (Icc 1 N) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp), hf, zero_add]

private theorem sum_logStep_sq_le (N : ℕ) :
    (∑ n ∈ range N, primeHeadLogStep n ^ 2) ≤ 2 := by
  calc
    _ ≤ ∑ n ∈ range (N + 1), primeHeadLogStep n ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ N)) (fun _ _ _ => sq_nonneg _)
    _ = ∑ n ∈ Icc 1 N, primeHeadLogStep n ^ 2 :=
      range_succ_eq_Icc_of_zero _ (by simp [primeHeadLogStep]) N
    _ ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hsq := mul_self_le_mul_self (logStep_nonneg n) (logStep_le_inv (mem_Icc.mp hn).1)
      simpa only [← sq, div_pow, one_pow] using hsq
    _ ≤ 2 := _root_.RHTower.Sieve.sum_inv_sq_le_two_of_pos (fun n hn => (mem_Icc.mp hn).1)

private theorem abs_sum_logStep_error_le (e : ℕ → ℝ) (N : ℕ) :
    |∑ n ∈ range N, e n * primeHeadLogStep n| ≤
      ∑ n ∈ range N, |e (n + 1)| / ((n : ℝ) + 1) := by
  calc
    _ ≤ ∑ n ∈ range N, |e n * primeHeadLogStep n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range (N + 1), |e n * primeHeadLogStep n| :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ N)) (fun _ _ _ => abs_nonneg _)
    _ = ∑ n ∈ range N, |e (n + 1)| * primeHeadLogStep (n + 1) := by
      rw [sum_range_succ']
      simp only [primeHeadLogStep, Nat.cast_zero, Nat.zero_add, Nat.cast_one, Real.log_one,
        Real.log_zero, sub_self, mul_zero, abs_zero, add_zero, abs_mul]
      apply sum_congr rfl
      intro n _
      change |e (n + 1)| * |primeHeadLogStep (n + 1)| =
        |e (n + 1)| * primeHeadLogStep (n + 1)
      rw [abs_of_nonneg (logStep_nonneg (n + 1))]
    _ ≤ _ := by
      apply sum_le_sum
      intro n _
      have h := mul_le_mul_of_nonneg_left (logStep_le_inv (Nat.succ_pos n)) (abs_nonneg (e (n + 1)))
      simpa only [Nat.cast_succ, mul_one_div] using h

private theorem tendsto_logStep_error {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, e n * primeHeadLogStep n) / Real.log N)
      atTop (𝓝 0) := by
  have he' : Tendsto (fun n : ℕ => |e (n + 1)|) atTop (𝓝 0) := by
    simpa only [Function.comp_def, abs_zero] using (he.comp (tendsto_add_atTop_nat 1)).abs
  apply squeeze_zero_norm' ?_ (tendsto_harmonicWeighted_error_zero he')
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog]
  exact div_le_div_of_nonneg_right (abs_sum_logStep_error_le e N) hlog.le

private theorem tendsto_logStep_sq_div_log :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, primeHeadLogStep n ^ 2) / Real.log N)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => (2 : ℝ) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog,
    abs_of_nonneg (sum_nonneg fun n _ => sq_nonneg (primeHeadLogStep n))]
  exact div_le_div_of_nonneg_right (sum_logStep_sq_le N) hlog.le

private theorem sum_log_mul_logStep (N : ℕ) :
    (∑ n ∈ range N, Real.log n * primeHeadLogStep n) =
      (Real.log N ^ 2 - ∑ n ∈ range N, primeHeadLogStep n ^ 2) / 2 := by
  have htel := sum_range_sub (fun n : ℕ => Real.log (n : ℝ) ^ 2) N
  simp only [Nat.cast_zero, Real.log_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), sub_zero] at htel
  have hterm (n : ℕ) : Real.log (n + 1 : ℕ) ^ 2 - Real.log n ^ 2 =
      primeHeadLogStep n ^ 2 + 2 * (Real.log n * primeHeadLogStep n) := by
    unfold primeHeadLogStep
    ring
  simp_rw [hterm] at htel
  rw [sum_add_distrib, ← mul_sum] at htel
  linarith only [htel]

private def primeHeadMertensError (N : ℕ) : ℝ :=
  mertensSum N - Real.log N + Real.eulerMascheroniConstant

private theorem tendsto_primeHeadMertensError :
    Tendsto primeHeadMertensError atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => mertensSum N - Real.log N + Real.eulerMascheroniConstant)
    atTop (𝓝 0)
  simpa only [neg_add_cancel] using
    tendsto_mertensSum_sub_log.add_const Real.eulerMascheroniConstant

private theorem primeHeadLogMoment_identity (N : ℕ) :
    (∑ n ∈ Icc 1 N, vonMangoldt n / (n : ℝ) * Real.log n) - Real.log N ^ 2 / 2 =
      Real.log N * primeHeadMertensError N +
        (∑ n ∈ range N, primeHeadLogStep n ^ 2) / 2 -
          ∑ n ∈ range N, primeHeadMertensError n * primeHeadLogStep n := by
  have hprefix (k : ℕ) :
      _root_.RHTower.WeilAbscissa.rampPartial (fun n => vonMangoldt n / (n : ℝ)) k =
      mertensSum k := by
    exact range_succ_eq_Icc_of_zero _ (by simp) k
  have hlogsum : (∑ n ∈ range (N + 1), vonMangoldt n / (n : ℝ) * Real.log n) =
      ∑ n ∈ Icc 1 N, vonMangoldt n / (n : ℝ) * Real.log n :=
    range_succ_eq_Icc_of_zero _ (by simp) N
  have h := _root_.RHTower.WeilAbscissa.sum_mul_log_sub_eq
    (fun n => vonMangoldt n / (n : ℝ)) N
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hlogsum] at h
  change _root_.RHTower.WeilAbscissa.rampPartial
    (fun n => vonMangoldt n / (n : ℝ)) N * Real.log N - _ = _ at h
  rw [hprefix] at h
  have he (n : ℕ) : mertensSum n =
      Real.log n - Real.eulerMascheroniConstant + primeHeadMertensError n := by
    unfold primeHeadMertensError
    ring
  simp only [hprefix] at h
  rw [← sum_sub_distrib] at h
  simp only [← mul_sub] at h
  change _ = ∑ n ∈ range N, mertensSum n * primeHeadLogStep n at h
  simp_rw [he] at h
  simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum] at h
  have ht : (∑ n ∈ range N, primeHeadLogStep n) = Real.log N :=
    _root_.RHTower.WeilAbscissa.telescope_log N
  rw [ht, sum_log_mul_logStep] at h
  linear_combination -h

/-- The log-weighted Mertens head has half-square main term with error smaller than one logarithm. -/
theorem tendsto_primeHeadLogMoment_remainder :
    Tendsto (fun N : ℕ =>
      ((∑ n ∈ Icc 1 N, vonMangoldt n / (n : ℝ) * Real.log n) - Real.log N ^ 2 / 2) /
        Real.log N) atTop (𝓝 0) := by
  have h := (tendsto_primeHeadMertensError.add (tendsto_logStep_sq_div_log.div_const 2)).sub
    (tendsto_logStep_error tendsto_primeHeadMertensError)
  simp only [zero_div, add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  rw [primeHeadLogMoment_identity]
  field_simp [hlog]

#print axioms tendsto_primeHeadLogMoment_remainder

end
end GaloisForLFunctions.SuccessorShellArithmetic
