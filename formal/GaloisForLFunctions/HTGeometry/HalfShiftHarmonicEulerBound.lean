import Mathlib

/-!
# The half-shifted harmonic upper bound for the Euler–Mascheroni constant

The sequence `H_n − log(n + 1/2)` decreases to `γ`.  Its step is
`1/(n+1) − log((2n+3)/(2n+1))`, and `log((2n+3)/(2n+1)) = 2 artanh(1/(2n+2)) ≥ 1/(n+1)` by the
first term of the artanh series.  Hence `γ ≤ H_n − log(n + 1/2)` for every `n`, with error of
order `1/(24n²)` instead of the `1/(2n)` of the classical bound `γ ≤ H_n − log n`.

The same series gives the elementary logarithm floors used alongside it: the odd partial sums
`Σ_{k<N} 2x^{2k+1}/(2k+1) ≤ log((1+x)/(1−x))` for `0 ≤ x < 1`, and their first case
`2(x−1)/(x+1) ≤ log x` for `x ≥ 1`.
-/

open Real Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Odd partial sums of the artanh series bound `log(1+x) − log(1−x)` from below. -/
theorem sum_range_artanh_le_log_sub_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) ≤
      Real.log (1 + x) - Real.log (1 - x) :=
  sum_le_hasSum (Finset.range N) (fun k _ => by positivity)
    (Real.hasSum_log_sub_log_of_abs_lt_one (by rw [abs_of_nonneg h0]; exact h1))

/-- `2(x−1)/(x+1) ≤ log x` for `x ≥ 1`. -/
theorem two_mul_sub_one_div_add_one_le_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have hx1 : 0 < x + 1 := by linarith
  set y := (x - 1) / (x + 1) with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hx1.le
  have hy1 : y < 1 := (div_lt_one hx1).2 (by linarith)
  have h := sum_range_artanh_le_log_sub_log hy0 hy1 1
  simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, mul_zero, zero_add,
    div_one, mul_one, pow_one] at h
  have hp : 0 < 1 + y := by linarith
  have hm : 0 < 1 - y := by linarith
  have hq : (1 + y) / (1 - y) = x := by
    rw [hy]
    field_simp
    ring
  rw [← Real.log_div hp.ne' hm.ne', hq] at h
  calc 2 * (x - 1) / (x + 1) = 2 * y := by rw [hy]; ring
    _ ≤ Real.log x := h

/-- The step of the half-shifted sequence: `1/(n+1) ≤ log(n + 3/2) − log(n + 1/2)`. -/
theorem inv_succ_le_log_add_half_step (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1 + 1 / 2) - Real.log ((n : ℝ) + 1 / 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hb : 0 < (n : ℝ) + 1 + 1 / 2 := by linarith
  have hx : 1 ≤ ((n : ℝ) + 1 + 1 / 2) / ((n : ℝ) + 1 / 2) := by
    rw [le_div_iff₀ ha]
    linarith
  have h := two_mul_sub_one_div_add_one_le_log hx
  rw [Real.log_div hb.ne' ha.ne'] at h
  calc 1 / ((n : ℝ) + 1) =
        2 * (((n : ℝ) + 1 + 1 / 2) / ((n : ℝ) + 1 / 2) - 1) /
          (((n : ℝ) + 1 + 1 / 2) / ((n : ℝ) + 1 / 2) + 1) := by
        field_simp
        ring
    _ ≤ _ := h

/-- `H_n − log(n + 1/2)` is antitone. -/
theorem antitone_harmonic_sub_log_add_half :
    Antitone fun n : ℕ => (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have h := inv_succ_le_log_add_half_step n
  rw [harmonic_succ]
  push_cast
  rw [one_div] at h
  linarith

/-- `H_n − log(n + 1/2) → γ`. -/
theorem tendsto_harmonic_sub_log_add_half :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2)) atTop
      (𝓝 eulerMascheroniConstant) := by
  have hshift : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1 / 2) - Real.log n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 + (1 / 2 : ℝ) / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)).const_add 1
    have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1)
    rw [Real.log_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply]
    rw [← Real.log_div (by positivity) hn'.ne']
    congr 1
    field_simp
  have h := tendsto_harmonic_sub_log.sub hshift
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  ring

/-- **The half-shifted harmonic bound**: `γ ≤ H_n − log(n + 1/2)` for every `n`. -/
theorem eulerMascheroniConstant_le_harmonic_sub_log_add_half (n : ℕ) :
    eulerMascheroniConstant ≤ (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2) :=
  antitone_harmonic_sub_log_add_half.le_of_tendsto tendsto_harmonic_sub_log_add_half n

end GaloisForLFunctions.HTGeometry
