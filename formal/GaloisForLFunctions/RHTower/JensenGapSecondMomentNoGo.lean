import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Jensen gap is not controlled by mean and variance

The mollified ceiling for the logarithmic mean of `|ζ|` on the critical line loses exactly the
Jensen gap `log E Y − E log Y` for `Y = |ζΨ|²/E|ζΨ|²`.  The mollified second and fourth moments
of `ζΨ` give the mean and variance of `Y`.  This module records that such data can never force a
positive Jensen gap: for every prescribed variance `v > 0` and every `ε > 0` there is a two-point
distribution with mean `1` and variance `v` whose Jensen gap is below `ε` — a rare far spike
carries the whole variance while the bulk sits next to `1`.  Improving the ceiling therefore
needs distributional information beyond the fourth mollified moment (an eighth moment, or a
tail/small-ball law), not sharper mean values.
-/

namespace RHTower

/-- **Mean and variance do not bound the Jensen gap.**  A two-point law `y₁ = 1 − a` with
probability `1 − p` and `y₂ = 1 + v/a` with probability `p = a²/(v + a²)` has mean `1`, second
moment `1 + v`, and Jensen gap `log(E Y) − E log Y < ε` once `a` is small. -/
theorem exists_twoPoint_mean_one_variance_jensen_gap_lt {v ε : ℝ} (hv : 0 < v) (hε : 0 < ε) :
    ∃ p y₁ y₂ : ℝ, 0 < p ∧ p < 1 ∧ 0 < y₁ ∧ 0 < y₂ ∧
      (1 - p) * y₁ + p * y₂ = 1 ∧ (1 - p) * y₁ ^ (2 : ℕ) + p * y₂ ^ (2 : ℕ) = 1 + v ∧
      Real.log ((1 - p) * y₁ + p * y₂) - ((1 - p) * Real.log y₁ + p * Real.log y₂) < ε := by
  set a : ℝ := min (1 / 4) (ε / 4) with ha
  have ha0 : 0 < a := lt_min (by norm_num) (by linarith)
  have ha1 : a ≤ 1 / 4 := min_le_left _ _
  have haε : a ≤ ε / 4 := min_le_right _ _
  have hva : 0 < v + a ^ (2 : ℕ) := by positivity
  set p : ℝ := a ^ (2 : ℕ) / (v + a ^ (2 : ℕ)) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p < 1 := by
    rw [hp, div_lt_one hva]
    linarith
  have hmean : (1 - p) * (1 - a) + p * (1 + v / a) = 1 := by
    rw [hp]
    field_simp
    ring
  refine ⟨p, 1 - a, 1 + v / a, hp0, hp1, by linarith, by positivity, hmean, ?_, ?_⟩
  · rw [hp]
    field_simp
    ring
  · rw [hmean, Real.log_one, zero_sub]
    have hlog2 : 0 ≤ Real.log (1 + v / a) := by
      apply Real.log_nonneg
      have : 0 ≤ v / a := by positivity
      linarith
    have h1a : 0 < 1 - a := by linarith
    have hlog1 : 1 - (1 - a)⁻¹ ≤ Real.log (1 - a) := Real.one_sub_inv_le_log_of_pos h1a
    have hinv : 1 - (1 - a)⁻¹ = -(a / (1 - a)) := by
      field_simp
      ring
    have hfrac : a / (1 - a) ≤ 2 * a := by
      rw [div_le_iff₀ h1a]
      nlinarith
    have h1p : 0 < 1 - p := by linarith
    have hterm1 : (1 - p) * Real.log (1 - a) ≥ -(2 * a) := by
      have : Real.log (1 - a) ≥ -(2 * a) := by linarith
      nlinarith
    have hterm2 : 0 ≤ p * Real.log (1 + v / a) := mul_nonneg hp0.le hlog2
    linarith

end RHTower
