import GaloisForLFunctions.RHTower.Sieve.PolylogLimits
import GaloisForLFunctions.RHTower.Sieve.RhoLimitPieces

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


/-- The window length is negligible against the square root of the outer scale, even against a
polynomial factor. -/
theorem tendsto_rpow_log_mul_cardLength_div_sqrt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (c : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c * (cardLength β x / Real.sqrt x)) atTop (𝓝 0) := by
  have hmaj := tendsto_rpow_log_mul_exp_neg (c := c) (a := (1 : ℝ) / 2) (by norm_num)
  have hneg : Tendsto (fun x : ℝ => (Real.log x) ^ (β - 1)) atTop (𝓝 0) :=
    tendsto_rpow_log_of_neg (by linarith)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hlogx.le c
    exact mul_nonneg hpow (div_nonneg (cardLength_pos β x).le (Real.sqrt_nonneg x))
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (16 : ℝ),
      Tendsto.eventually_le_const (show (0:ℝ) < 1 / 4 by norm_num) hneg] with x hx1 hlog16 hsmall
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hlogx.le c
    have hquarter : (Real.log x) ^ β ≤ Real.log x / 4 := by
      have hsplit : (Real.log x) ^ β = (Real.log x) ^ (β - 1) * Real.log x := by
        rw [← Real.rpow_add_one (ne_of_gt hlogx)]
        congr 1
        ring
      rw [hsplit]
      have := mul_le_mul_of_nonneg_right hsmall hlogx.le
      linarith [this]
    have hhalf : (Real.log x) ^ ((1 : ℝ) / 2) ≤ Real.log x / 4 := by
      have hsq : ((Real.log x) ^ ((1 : ℝ) / 2)) ^ 2 = Real.log x := by
        rw [← Real.rpow_natCast ((Real.log x) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hlogx.le]
        norm_num
      have hs0 : (0 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hlogx.le _
      nlinarith [hsq, hs0, hlog16]
    have hval : cardLength β x / Real.sqrt x
        = Real.exp ((Real.log x) ^ β - Real.log x / 2) := by
      rw [cardLength, sqrt_eq_exp_half_log hx0, ← Real.exp_sub]
    rw [hval]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hpow
    linarith [hquarter, hhalf]

/-- A power of the logarithm is negligible against the sifting cutoff. -/
theorem tendsto_rpow_log_div_siftStart {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c / ((siftStart a x : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hmaj := tendsto_rpow_log_mul_exp_neg (c := c) (a := a) ha
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    exact div_nonneg (Real.rpow_nonneg hlogx.le c) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hlogx.le c
    have hQ := eventually_siftStart_ge (c := a) x
    have hQ0 : (0 : ℝ) < Real.exp ((Real.log x) ^ a) := Real.exp_pos _
    have hinv : 1 / ((siftStart a x : ℕ) : ℝ) ≤ Real.exp (-((Real.log x) ^ a)) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hQ0 hQ
    calc (Real.log x) ^ c / ((siftStart a x : ℕ) : ℝ)
        = (Real.log x) ^ c * (1 / ((siftStart a x : ℕ) : ℝ)) := by ring
      _ ≤ (Real.log x) ^ c * Real.exp (-((Real.log x) ^ a)) :=
          mul_le_mul_of_nonneg_left hinv hpow

end

end RHTower.Sieve
