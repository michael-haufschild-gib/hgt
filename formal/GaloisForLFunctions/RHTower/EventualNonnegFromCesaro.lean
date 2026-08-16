import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A strictly negative Cesàro mean forbids eventual nonnegativity

If the Cesàro mean of a continuous function converges to a strictly negative limit, the function is
strictly negative at arbitrarily late times: an eventually nonnegative tail would make the mean
bounded below by a constant divided by the horizon, hence nonnegative in the limit.  This is the
step that upgrades a strictly negative shell mean to a violation of an eventual criterion.
-/

open Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- **A strictly negative Cesàro mean produces arbitrarily late strictly negative values.** -/
theorem exists_lt_zero_of_tendsto_cesaro_neg {f : ℝ → ℝ} {L : ℝ} (hL : L < 0)
    (hcont : Continuous f)
    (hces : Tendsto (fun T : ℝ => (1 / T) * ∫ t in (1 : ℝ)..T, f t) atTop (𝓝 L))
    (T₀ : ℝ) : ∃ t, T₀ < t ∧ f t < 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  set S : ℝ := max T₀ 1 + 1 with hSdef
  have hS1 : (1 : ℝ) ≤ S := by
    have := le_max_right T₀ 1
    rw [hSdef]
    linarith
  have hST₀ : T₀ < S := by
    have := le_max_left T₀ 1
    rw [hSdef]
    linarith
  set C : ℝ := ∫ t in (1 : ℝ)..S, f t with hCdef
  have hlow : ∀ᶠ T : ℝ in atTop, C / T ≤ (1 / T) * ∫ t in (1 : ℝ)..T, f t := by
    filter_upwards [eventually_ge_atTop S, eventually_gt_atTop (0 : ℝ)] with T hTS hTpos
    have hadj : (∫ t in (1 : ℝ)..S, f t) + ∫ t in (S : ℝ)..T, f t = ∫ t in (1 : ℝ)..T, f t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    have htail : (0 : ℝ) ≤ ∫ t in (S : ℝ)..T, f t := by
      refine intervalIntegral.integral_nonneg hTS fun t ht => ?_
      exact hcon t (lt_of_lt_of_le hST₀ ht.1)
    have hCle : C ≤ ∫ t in (1 : ℝ)..T, f t := by
      rw [← hadj, hCdef]
      linarith
    have hinv : (0 : ℝ) < 1 / T := by positivity
    calc C / T = (1 / T) * C := by ring
      _ ≤ (1 / T) * ∫ t in (1 : ℝ)..T, f t := mul_le_mul_of_nonneg_left hCle hinv.le
  have hCT : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hLnn : (0 : ℝ) ≤ L := le_of_tendsto_of_tendsto hCT hces hlow
  linarith

end

end RHTower
