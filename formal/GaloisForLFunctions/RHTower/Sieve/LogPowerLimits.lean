import Mathlib

/-!
# Negative powers of the logarithm

The parameter substitution compares quantities of the form `(log x)^{-c}` with `1/log x`.  This file
records the two limits that comparison needs, in the `rpow` form the substitution produces.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **A negative power of the logarithm vanishes.** -/
theorem tendsto_log_rpow_neg {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ (-δ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop

/-- **A negative power of the logarithm beats `1/log x` when the exponent exceeds one.** -/
theorem tendsto_log_rpow_neg_mul_log {c : ℝ} (hc : 1 < c) :
    Tendsto (fun x : ℝ => (Real.log x) ^ (-c) * Real.log x) atTop (𝓝 0) := by
  have hδ : 0 < c - 1 := by linarith
  refine (tendsto_log_rpow_neg hδ).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [show -(c - 1) = -c + 1 by ring, Real.rpow_add hlog, Real.rpow_one]

/-- **The sieve saving beats `1/log x` in the admissible window.**  If `log P₁ ≤ (log hN)^a` and
`log hN ≥ (log x)^β`, then `(log P₁/log hN)²·log x → 0` exactly when `2β(1−a) > 1`. -/
theorem tendsto_logRatio_sq_mul_log {a β : ℝ} (ha1 : a ≤ 1) (hβ : 0 < β)
    (hgap : 1 < 2 * β * (1 - a)) {P₁ hN : ℝ → ℝ}
    (hP : ∀ᶠ x in atTop, 0 ≤ Real.log (P₁ x) ∧ Real.log (P₁ x) ≤ (Real.log (hN x)) ^ a)
    (hh : ∀ᶠ x in atTop, (Real.log x) ^ β ≤ Real.log (hN x)) :
    Tendsto (fun x : ℝ => (Real.log (P₁ x) / Real.log (hN x)) ^ 2 * Real.log x)
      atTop (𝓝 0) := by
  have hmaj := tendsto_log_rpow_neg_mul_log (c := 2 * β * (1 - a)) hgap
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hP, hh, Filter.eventually_gt_atTop (1 : ℝ)] with x _ _ hx
    have : (0 : ℝ) ≤ Real.log x := (Real.log_pos hx).le
    positivity
  · filter_upwards [hP, hh, Filter.eventually_gt_atTop (Real.exp 1)] with x hPx hhx hx
    have hlx1 : (1 : ℝ) < Real.log x := by
      have := Real.log_lt_log (Real.exp_pos 1) hx
      rwa [Real.log_exp] at this
    have hlx0 : (0 : ℝ) < Real.log x := by linarith
    have hLbig : (1 : ℝ) ≤ (Real.log x) ^ β := Real.one_le_rpow hlx1.le hβ.le
    have hlh1 : (1 : ℝ) ≤ Real.log (hN x) := le_trans hLbig hhx
    have hlh0 : (0 : ℝ) < Real.log (hN x) := by linarith
    -- the ratio is at most `(log hN)^{a-1}`
    have hratio : (Real.log (P₁ x) / Real.log (hN x)) ^ 2
        ≤ ((Real.log (hN x)) ^ (a - 1)) ^ 2 := by
      refine pow_le_pow_left₀ (div_nonneg hPx.1 hlh0.le) ?_ 2
      rw [div_le_iff₀ hlh0]
      have hstep : (Real.log (hN x)) ^ (a - 1) * Real.log (hN x)
          = (Real.log (hN x)) ^ a := by
        rw [show (a : ℝ) = (a - 1) + 1 by ring]
        rw [Real.rpow_add hlh0, Real.rpow_one]
        ring_nf
      rw [hstep]
      exact hPx.2
    have hpow : ((Real.log (hN x)) ^ (a - 1)) ^ 2
        = (Real.log (hN x)) ^ (2 * (a - 1)) := by
      rw [← Real.rpow_natCast ((Real.log (hN x)) ^ (a - 1)) 2, ← Real.rpow_mul hlh0.le]
      norm_num
      ring_nf
    have hbase : (Real.log (hN x)) ^ (2 * (a - 1))
        ≤ ((Real.log x) ^ β) ^ (2 * (a - 1)) := by
      refine Real.rpow_le_rpow_of_nonpos (by linarith) hhx ?_
      nlinarith [ha1]
    have hcomp : ((Real.log x) ^ β) ^ (2 * (a - 1))
        = (Real.log x) ^ (-(2 * β * (1 - a))) := by
      rw [← Real.rpow_mul hlx0.le]
      congr 1
      ring
    calc (Real.log (P₁ x) / Real.log (hN x)) ^ 2 * Real.log x
        ≤ ((Real.log (hN x)) ^ (a - 1)) ^ 2 * Real.log x :=
          mul_le_mul_of_nonneg_right hratio hlx0.le
      _ = (Real.log (hN x)) ^ (2 * (a - 1)) * Real.log x := by rw [hpow]
      _ ≤ ((Real.log x) ^ β) ^ (2 * (a - 1)) * Real.log x :=
          mul_le_mul_of_nonneg_right hbase hlx0.le
      _ = (Real.log x) ^ (-(2 * β * (1 - a))) * Real.log x := by rw [hcomp]

/-- **A stretched exponential in the logarithm vanishes.**  This is `1/h` for the short-interval
length `h = exp((log x)^β)` of the Route E cards. -/
theorem tendsto_exp_neg_log_rpow {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun x : ℝ => Real.exp (-((Real.log x) ^ β))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hpow

end RHTower.Sieve
