import Mathlib

/-!
# The elementary integer gap for logarithms of ratios

For distinct positive integers the logarithm of their ratio is bounded below by the relative
integer gap.  This is the elementary estimate that controls the edge coboundary norm, in place of
any effective transcendence bound.
-/

namespace GaloisForLFunctions.HTGeometry

open Real

/-- `log x ≥ 1 − 1/x` for positive `x`. -/
theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := x⁻¹) (inv_pos.2 hx)
  rw [Real.log_inv] at h
  linarith

/-- **The integer gap bound.**  For `0 < b < a` the logarithm of `a/b` is at least the relative
gap `(a − b)/a`. -/
theorem gap_div_le_log_div {a b : ℕ} (hb : 0 < b) (hab : b < a) :
    ((a : ℝ) - b) / a ≤ Real.log ((a : ℝ) / b) := by
  have ha : (0 : ℝ) < a := by
    exact_mod_cast lt_trans hb hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpos : (0 : ℝ) < (a : ℝ) / b := div_pos ha hbR
  have h := one_sub_inv_le_log hpos
  have hinv : ((a : ℝ) / b)⁻¹ = (b : ℝ) / a := by
    rw [inv_div]
  rw [hinv] at h
  have hrw : 1 - (b : ℝ) / a = ((a : ℝ) - b) / a := by
    field_simp
  rw [hrw] at h
  exact h

/-- **The integer gap bound, symmetric form.** -/
theorem gap_div_le_abs_log_div {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    |(a : ℝ) - b| / max (a : ℝ) b ≤ |Real.log ((a : ℝ) / b)| := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hgap := gap_div_le_log_div ha hlt
    have hmax : max (a : ℝ) b = (b : ℝ) := by
      refine max_eq_right ?_
      exact_mod_cast hlt.le
    have habs : |(a : ℝ) - b| = (b : ℝ) - a := by
      rw [abs_sub_comm, abs_of_nonneg]
      have : (a : ℝ) ≤ b := by exact_mod_cast hlt.le
      linarith
    have hlog : Real.log ((a : ℝ) / b) = -Real.log ((b : ℝ) / a) := by
      rw [← Real.log_inv, inv_div]
    rw [hmax, habs, hlog, abs_neg]
    exact le_trans hgap (le_abs_self _)
  · have hgap := gap_div_le_log_div hb hlt
    have hmax : max (a : ℝ) b = (a : ℝ) := by
      refine max_eq_left ?_
      exact_mod_cast hlt.le
    have habs : |(a : ℝ) - b| = (a : ℝ) - b := by
      rw [abs_of_nonneg]
      have : (b : ℝ) ≤ a := by exact_mod_cast hlt.le
      linarith
    rw [hmax, habs]
    exact le_trans hgap (le_abs_self _)

end GaloisForLFunctions.HTGeometry
