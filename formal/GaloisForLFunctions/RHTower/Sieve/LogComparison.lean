import GaloisForLFunctions.RHTower.Sieve.SmoothWidthChoice

/-!
# Comparing the two logarithmic variables

The saving is expressed in `t = (log(N+H))^{1/10}` and the price in `v = (log N)^{1/20}`.  Since
`N ≤ N+H ≤ 2N`, the two are comparable: `v² ≤ t ≤ 2v²`.  The lower bound is what lets the saving be
measured against the price; the upper bound is what keeps the polynomial in `t` a polynomial in `v²`.
-/

namespace RHTower.Sieve

open Real

/-- `v² ≤ t`. -/
theorem sq_le_logRpow {N H : ℝ} (hlog : 1 ≤ Real.log N) (hN : 0 < N) (hH : 0 ≤ H) :
    ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 ≤ (Real.log (N + H)) ^ ((1 : ℝ) / 10) := by
  have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
  rw [rpow_twentieth_sq hlog0]
  refine Real.rpow_le_rpow hlog0 ?_ (by norm_num)
  exact Real.log_le_log hN (by linarith)

/-- `t ≤ 2v²`. -/
theorem logRpow_le_two_sq {N H : ℝ} (hlog : 1 ≤ Real.log N) (hN : 0 < N) (hH : 0 ≤ H)
    (hHN : H ≤ N) :
    (Real.log (N + H)) ^ ((1 : ℝ) / 10) ≤ 2 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 := by
  have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hbound : Real.log (N + H) ≤ 2 * Real.log N := by
    have h1 : Real.log (N + H) ≤ Real.log (2 * N) := by
      refine Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 * N) = Real.log 2 + Real.log N :=
      Real.log_mul (by norm_num) (ne_of_gt hN)
    linarith
  have hstep : (Real.log (N + H)) ^ ((1 : ℝ) / 10)
      ≤ (2 * Real.log N) ^ ((1 : ℝ) / 10) := by
    refine Real.rpow_le_rpow ?_ hbound (by norm_num)
    have hNH : (1 : ℝ) ≤ N + H := by
      have : (1 : ℝ) ≤ N := by
        have := Real.exp_le_exp.2 hlog
        rw [Real.exp_log hN] at this
        have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        linarith
      linarith
    exact Real.log_nonneg hNH
  have hsplit : (2 * Real.log N) ^ ((1 : ℝ) / 10)
      = (2 : ℝ) ^ ((1 : ℝ) / 10) * (Real.log N) ^ ((1 : ℝ) / 10) :=
    Real.mul_rpow (by norm_num) hlog0
  have htwo : (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hpos : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hlog0 _
  rw [rpow_twentieth_sq hlog0]
  calc (Real.log (N + H)) ^ ((1 : ℝ) / 10)
      ≤ (2 * Real.log N) ^ ((1 : ℝ) / 10) := hstep
    _ = (2 : ℝ) ^ ((1 : ℝ) / 10) * (Real.log N) ^ ((1 : ℝ) / 10) := hsplit
    _ ≤ 2 * (Real.log N) ^ ((1 : ℝ) / 10) := mul_le_mul_of_nonneg_right htwo hpos

end RHTower.Sieve
