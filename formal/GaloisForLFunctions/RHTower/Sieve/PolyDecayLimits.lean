import GaloisForLFunctions.RHTower.Sieve.PolylogLimits

/-!
# Polynomial factors against the two outer scales

Every power of the logarithm is negligible against the square root of the outer scale and against
the window length.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The square root of the outer scale, exponentially. -/
theorem sqrt_eq_exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf

/-- A power of the logarithm is negligible against the square root of the outer scale. -/
theorem tendsto_rpow_log_div_sqrt (c : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c / Real.sqrt x) atTop (𝓝 0) := by
  have hmaj := tendsto_rpow_log_mul_exp_neg (c := c) (a := (1 : ℝ) / 2) (by norm_num)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hlogx.le c
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    exact div_nonneg hpow hsx.le
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)] with x hx1 hlog4
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hlogx.le c
    have hhalf : (Real.log x) ^ ((1 : ℝ) / 2) ≤ Real.log x / 2 := by
      have hsq : ((Real.log x) ^ ((1 : ℝ) / 2)) ^ 2 = Real.log x := by
        rw [← Real.rpow_natCast ((Real.log x) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hlogx.le]
        norm_num
      have hs0 : (0 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hlogx.le _
      nlinarith [hsq, hs0, hlog4]
    have hinv : 1 / Real.sqrt x = Real.exp (-(Real.log x / 2)) := by
      rw [sqrt_eq_exp_half_log hx0, one_div, ← Real.exp_neg]
    calc (Real.log x) ^ c / Real.sqrt x = (Real.log x) ^ c * (1 / Real.sqrt x) := by ring
      _ = (Real.log x) ^ c * Real.exp (-(Real.log x / 2)) := by rw [hinv]
      _ ≤ (Real.log x) ^ c * Real.exp (-((Real.log x) ^ ((1 : ℝ) / 2))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hpow

/-- A power of the logarithm is negligible against the window length. -/
theorem tendsto_rpow_log_div_cardLength {β : ℝ} (hβ0 : 0 < β) (c : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c / cardLength β x) atTop (𝓝 0) := by
  have hmaj := tendsto_rpow_log_mul_exp_neg (c := c) (a := β) hβ0
  refine hmaj.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
  have hinv : 1 / cardLength β x = Real.exp (-((Real.log x) ^ β)) := by
    rw [cardLength, one_div, ← Real.exp_neg]
  calc (Real.log x) ^ c * Real.exp (-((Real.log x) ^ β))
      = (Real.log x) ^ c * (1 / cardLength β x) := by rw [hinv]
    _ = (Real.log x) ^ c / cardLength β x := by ring

end

end RHTower.Sieve
