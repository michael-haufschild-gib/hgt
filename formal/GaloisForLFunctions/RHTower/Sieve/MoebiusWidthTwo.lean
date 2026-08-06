import GaloisForLFunctions.RHTower.Sieve.MoebiusKappaTwoRate

/-!
# The smoothing width balanced against the width-`log^{-2}` saving

The contour bound costs `(N/H)²` and saves `exp(-t/18)` with `t = (log(N+H+1))^{1/3}`, while
replacing the smoothed sum by the sharp one costs `H`.  Writing `N/H = exp(t/54)` balances the
three: the price becomes `exp(t/27)`, leaving `exp(-t/54)`, and the comparison costs the same
`N exp(-t/54)`.

Any wider window makes the comparison dominate; any narrower one makes the squared price dominate.
The corpus's `smoothWidth`, tuned to the exponent-nine saving `exp(-c(log N)^{1/10})`, is far too
wide here.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The smoothing ratio balanced against the width-`log^{-2}` saving. -/
noncomputable def smoothRatioTwo (N : ℝ) : ℝ := Real.exp ((Real.log N) ^ ((1 : ℝ) / 3) / 54)

/-- The smoothing width. -/
noncomputable def smoothWidthTwo (N : ℝ) : ℝ := N / smoothRatioTwo N

theorem smoothRatioTwo_pos (N : ℝ) : 0 < smoothRatioTwo N := Real.exp_pos _

theorem one_le_smoothRatioTwo {N : ℝ} (hN : 1 ≤ Real.log N) : 1 ≤ smoothRatioTwo N := by
  rw [smoothRatioTwo]
  refine Real.one_le_exp ?_
  have h : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  linarith

theorem smoothWidthTwo_le {N : ℝ} (hN0 : 0 ≤ N) (hN : 1 ≤ Real.log N) :
    smoothWidthTwo N ≤ N := by
  rw [smoothWidthTwo]
  exact div_le_self hN0 (one_le_smoothRatioTwo hN)

theorem div_smoothWidthTwo {N : ℝ} (hN0 : 0 < N) : N / smoothWidthTwo N = smoothRatioTwo N := by
  rw [smoothWidthTwo]
  field_simp

/-- The cube root of the logarithm is at most the logarithm. -/
theorem rpow_third_le_log {N : ℝ} (hN : 1 ≤ Real.log N) :
    (Real.log N) ^ ((1 : ℝ) / 3) ≤ Real.log N := by
  calc (Real.log N) ^ ((1 : ℝ) / 3) ≤ (Real.log N) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ = Real.log N := Real.rpow_one _

theorem one_le_smoothWidthTwo {N : ℝ} (hN0 : 0 < N) (hN : 1 ≤ Real.log N) :
    1 ≤ smoothWidthTwo N := by
  rw [smoothWidthTwo, le_div_iff₀ (smoothRatioTwo_pos N), one_mul, smoothRatioTwo]
  have ht := rpow_third_le_log hN
  have ht0 : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  calc Real.exp ((Real.log N) ^ ((1 : ℝ) / 3) / 54) ≤ Real.exp (Real.log N) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = N := Real.exp_log hN0

/-- **The rate's coefficient is a constant times the square of the smoothing ratio.** -/
theorem coeffMajorantTwo_le {C C' Ms L : ℝ} (_hC : 0 ≤ C) (hC' : 0 ≤ C') (hMs : 0 ≤ Ms)
    (hL : 0 ≤ L) :
    coeffMajorantTwo C C' Ms L
      ≤ (80 * Real.exp (22 / 4) * C + 16 * Ms * C' + 9 * Ms * (1 + 2 * C)) * (L + 2) ^ 2 := by
  rw [coeffMajorantTwo]
  have hsq : L + 2 ≤ (L + 2) ^ 2 := by nlinarith
  have hsq4 : (4 : ℝ) ≤ (L + 2) ^ 2 := by nlinarith
  have t2 : 16 * Ms * (C' * (L + 2)) ≤ 16 * Ms * C' * (L + 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hMs) hC')
    linarith [h]
  have t3 : 9 * Ms * (4 + 2 * (C * (L + 2) ^ 2)) ≤ 9 * Ms * (1 + 2 * C) * (L + 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsq4
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hMs)
    linarith [h]
  linarith [t2, t3]

end RHTower.Sieve
