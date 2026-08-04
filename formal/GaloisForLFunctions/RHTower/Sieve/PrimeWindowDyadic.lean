import GaloisForLFunctions.RHTower.Sieve.MertensWindowSharp

/-!
# The dyadic prime window

The tail `∑_{p > z} p^{−σ}` at `σ = 1 + 1/log z` is summed dyadically, and each block needs the
reciprocal sum of a window of ratio two.  A one-sided Mertens bound is useless there — subtracting
two of them adds their additive constants and leaves `O(1)` per block, which over `≍ log z` blocks
gives `O(log z)`.  The sharp form of `MertensWindowSharp.lean` gives instead

    ∑_{y < p ≤ 2y} 1/p  ≤  (log 2 + 2C)/log y,      C = 2·mertensFirstConst + 1/2,

because `logLog(2y) − logLog y = log(1 + log 2/log y) ≤ log 2/log y`.  The decay in `y` is what makes
the dyadic sum converge.

Also recorded here is the elementary lower bound `u/2 ≤ 1 − e^{−u}` on `[0,1]`, which controls the
ratio of the geometric series appearing in that sum.
-/

namespace RHTower.Sieve

open Finset

/-- `1 − e^{−u} ≥ u/2` on `[0, 1]`, via `e^{−u} ≤ 1/(1+u)`. -/
theorem one_sub_exp_neg_ge {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hexp : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hle : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
  have hinv : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, inv_eq_one_div]
    refine div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hpos : (0 : ℝ) < 1 + u := by linarith
  have hstep : 1 - 1 / (1 + u) = u / (1 + u) := by
    field_simp
    ring
  have hhalf : u / 2 ≤ u / (1 + u) := by
    refine div_le_div_of_nonneg_left hu0 hpos (by linarith)
  linarith [hinv, hstep.le, hstep.ge, hhalf]

/-- The `logLog` increment across a dyadic step. -/
theorem logLog_two_mul_sub_le {y : ℕ} (hy : 2 ≤ y) :
    logLog (2 * y) - logLog y ≤ Real.log 2 / Real.log y := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hlogy : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hcast : ((2 * y : ℕ) : ℝ) = 2 * (y : ℝ) := by push_cast; ring
  have hlog2y : Real.log (2 * (y : ℝ)) = Real.log 2 + Real.log (y : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hy0)
  have hpos2y : (0 : ℝ) < Real.log 2 + Real.log (y : ℝ) := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  rw [logLog, logLog, hcast, hlog2y]
  have hdiff : Real.log (Real.log 2 + Real.log (y : ℝ)) - Real.log (Real.log (y : ℝ))
      = Real.log ((Real.log 2 + Real.log (y : ℝ)) / Real.log (y : ℝ)) := by
    rw [Real.log_div (ne_of_gt hpos2y) (ne_of_gt hlogy)]
  rw [hdiff]
  have hratio : (Real.log 2 + Real.log (y : ℝ)) / Real.log (y : ℝ)
      = 1 + Real.log 2 / Real.log (y : ℝ) := by
    field_simp
    ring
  rw [hratio]
  have hx : (0 : ℝ) ≤ Real.log 2 / Real.log (y : ℝ) := by
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hlog1 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + Real.log 2 / Real.log (y : ℝ))
  linarith

/-- **The reciprocal sum of a dyadic prime window.** -/
theorem sum_inv_dyadic_window_le {y : ℕ} (hy : 2 ≤ y) :
    ∑ p ∈ bigPrimeSet y (2 * y), 1 / (p : ℝ)
      ≤ (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log y := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hyb : y ≤ 2 * y := by omega
  have hb2 : 2 ≤ 2 * y := by omega
  have hbcast : ((2 * y : ℕ) : ℝ) = 2 * (y : ℝ) := by push_cast; ring
  have hlogb : Real.log (y : ℝ) ≤ Real.log ((2 * y : ℕ) : ℝ) := by
    rw [hbcast]
    refine Real.log_le_log (by linarith) (by linarith)
  have hC0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
    have := mertensFirstConst_nonneg
    linarith
  have habs := abs_le.1 (abs_sum_inv_bigPrimeSet_sub_le hy hyb)
  have hinc := logLog_two_mul_sub_le hy
  have hCb : (2 * mertensFirstConst + 1 / 2) / Real.log ((2 * y : ℕ) : ℝ)
      ≤ (2 * mertensFirstConst + 1 / 2) / Real.log (y : ℝ) := by
    refine div_le_div_of_nonneg_left hC0 hlogy hlogb
  have hsplit : (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log (y : ℝ)
      = Real.log 2 / Real.log (y : ℝ)
        + ((2 * mertensFirstConst + 1 / 2) / Real.log (y : ℝ)
          + (2 * mertensFirstConst + 1 / 2) / Real.log (y : ℝ)) := by
    field_simp
    ring
  rw [hsplit]
  linarith [habs.2, hinc, hCb]

end RHTower.Sieve
