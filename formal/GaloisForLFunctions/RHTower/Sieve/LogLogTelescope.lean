import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Telescoping the iterated logarithm

Partial summation against `1/log` produces the discrete sum

`T N = ∑_{2 ≤ i < N} (log (i+1) - log i) / log (i+1)`,

which is the discrete model of `∫ dt / (t log t)`.  Both bounds are obtained here by telescoping
`log ∘ log` rather than by an integral comparison, using only the two concavity inequalities

`(b - a)/b ≤ log b - log a ≤ (b - a)/a`  for `0 < a ≤ b`.

Applied with `a = log i`, `b = log (i+1)` they sandwich each term of `T N` between two consecutive
increments of `log ∘ log`, so

`log log (N+1) - log log 3 ≤ T N ≤ log log N - log log 2`.
-/

namespace RHTower.Sieve

open Finset

/-- Concavity of the logarithm, upper form. -/
theorem log_sub_log_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ (b - a) / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hdiv : 0 < b / a := div_pos hb ha
  have := Real.log_le_sub_one_of_pos hdiv
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at this
  have hrw : b / a - 1 = (b - a) / a := by field_simp
  linarith [this, hrw ▸ this]

/-- Concavity of the logarithm, lower form. -/
theorem le_log_sub_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hdiv : 0 < a / b := div_pos ha hb
  have := Real.log_le_sub_one_of_pos hdiv
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at this
  have hrw : a / b - 1 = -((b - a) / b) := by
    field_simp
    ring
  rw [hrw] at this
  linarith

/-- The iterated logarithm of a natural number, with the convention making it vanish below `2`. -/
noncomputable def logLog (i : ℕ) : ℝ := Real.log (Real.log i)

/-- The discrete model of `∫ dt / (t log t)`. -/
noncomputable def logLogIncrementSum (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 2 N, (Real.log (i + 1) - Real.log i) / Real.log (i + 1)

/-- The logarithm is positive from `2` on. -/
theorem log_pos_of_two_le {i : ℕ} (hi : 2 ≤ i) : 0 < Real.log i := by
  have : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  exact Real.log_pos (by linarith)

/-- Telescoping a difference over `Ico`. -/
theorem sum_Ico_telescope (F : ℕ → ℝ) {m N : ℕ} (h : m ≤ N) :
    ∑ i ∈ Finset.Ico m N, (F (i + 1) - F i) = F N - F m := by
  rw [Finset.sum_Ico_eq_sub _ h, Finset.sum_range_sub F, Finset.sum_range_sub F]
  ring

/-- **Upper telescoping bound.** -/
theorem logLogIncrementSum_le {N : ℕ} (hN : 2 ≤ N) :
    logLogIncrementSum N ≤ logLog N - logLog 2 := by
  have hterm : ∀ i ∈ Finset.Ico 2 N,
      (Real.log (i + 1) - Real.log i) / Real.log (i + 1) ≤ logLog (i + 1) - logLog i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Ico.1 hi).1
    have hlogi : 0 < Real.log i := log_pos_of_two_le hi2
    have hmono : Real.log i ≤ Real.log ((i : ℝ) + 1) := by
      refine Real.log_le_log (by positivity) (by linarith)
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have := le_log_sub_log hlogi hmono
    simp only [logLog, hcast]
    exact this
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [sum_Ico_telescope logLog hN]

/-- **Lower telescoping bound.** -/
theorem le_logLogIncrementSum {N : ℕ} (hN : 2 ≤ N) :
    logLog (N + 1) - logLog 3 ≤ logLogIncrementSum N := by
  have hterm : ∀ i ∈ Finset.Ico 2 N,
      logLog (i + 2) - logLog (i + 1)
        ≤ (Real.log (i + 1) - Real.log i) / Real.log (i + 1) := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Ico.1 hi).1
    have hiR : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
    have hlog1 : 0 < Real.log ((i : ℝ) + 1) := Real.log_pos (by linarith)
    have hmono : Real.log ((i : ℝ) + 1) ≤ Real.log ((i : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hstep := log_sub_log_le hlog1 hmono
    have hshift : Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1)
        ≤ Real.log ((i : ℝ) + 1) - Real.log i := by
      have hi0 : (0 : ℝ) < (i : ℝ) := by linarith
      have hratio : ((i : ℝ) + 2) / ((i : ℝ) + 1) ≤ ((i : ℝ) + 1) / (i : ℝ) := by
        have h1 : ((i : ℝ) + 2) / ((i : ℝ) + 1) = 1 + 1 / ((i : ℝ) + 1) := by
          field_simp
          ring
        have h2 : ((i : ℝ) + 1) / (i : ℝ) = 1 + 1 / (i : ℝ) := by
          field_simp
        have h3 : 1 / ((i : ℝ) + 1) ≤ 1 / (i : ℝ) :=
          one_div_le_one_div_of_le hi0 (by linarith)
        rw [h1, h2]
        linarith
      have hl : Real.log (((i : ℝ) + 2) / ((i : ℝ) + 1))
          ≤ Real.log (((i : ℝ) + 1) / (i : ℝ)) :=
        Real.log_le_log (by positivity) hratio
      rw [Real.log_div (by linarith) (by linarith),
        Real.log_div (by linarith) (by linarith)] at hl
      exact hl
    have hcast1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((i + 2 : ℕ) : ℝ) = (i : ℝ) + 2 := by push_cast; ring
    simp only [logLog, hcast1, hcast2]
    have hdiv : (Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1)) / Real.log ((i : ℝ) + 1)
        ≤ (Real.log ((i : ℝ) + 1) - Real.log i) / Real.log ((i : ℝ) + 1) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hshift (inv_nonneg.2 hlog1.le)
    exact le_trans hstep hdiv
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  have htel : ∑ i ∈ Finset.Ico 2 N, (logLog (i + 2) - logLog (i + 1))
      = logLog (N + 1) - logLog 3 := by
    have := sum_Ico_telescope (fun i => logLog (i + 1)) hN
    simpa using this
  rw [htel]

end RHTower.Sieve
