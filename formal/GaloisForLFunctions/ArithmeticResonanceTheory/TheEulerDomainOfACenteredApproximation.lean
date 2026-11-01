import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Centering a weight line moves the Euler domain

An affine coordinate `u = a s + b` sends the weight line `Re u = w/2` to
`Re s = 1/2` when `a/2 + b = w/2`. If the Euler abscissa in `u` is `d`,
its new value is `1/2 + (2d-w)/(2a)`. For curve zeta functions `d = w = 1`.
Thus a vanishing logarithmic mesh `a log q`, with `q ≥ 2`, cannot preserve
any fixed Euler half-plane. These are parameter identities; no theorem about
the existence or convergence of geometric approximants is assumed.
-/

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-- Exact distance between the centered weight line and the transformed Euler abscissa. -/
theorem centered_euler_abscissa {a b d w : ℝ} (ha : a ≠ 0)
    (hcenter : a / 2 + b = w / 2) :
    (d - b) / a = 1 / 2 + (2 * d - w) / (2 * a) := by
  field_simp
  nlinarith only [hcenter]

/-- The Euler gap times the frequency mesh is invariant under a centered rescaling. -/
theorem centered_euler_gap_mul_mesh {a b d w q : ℝ} (ha : a ≠ 0)
    (hcenter : a / 2 + b = w / 2) :
    ((d - b) / a - 1 / 2) * (a * Real.log q) =
      (d - w / 2) * Real.log q := by
  rw [centered_euler_abscissa ha hcenter]
  field_simp
  ring

/-- Keeping a centered curve's Euler abscissa at most one forces its scale to be at least one. -/
theorem centered_curve_euler_abscissa_le_one_iff {a b : ℝ} (ha : 0 < a)
    (hcenter : a / 2 + b = 1 / 2) :
    (1 - b) / a ≤ 1 ↔ 1 ≤ a := by
  rw [div_le_iff₀ ha]
  constructor <;> intro h <;> linarith only [hcenter, h]

/-- An explicit mesh threshold excludes every prescribed fixed Euler half-plane for curves. -/
theorem centered_curve_euler_abscissa_gt_of_small_mesh {a b q M : ℝ}
    (ha : 0 < a) (hq : 2 ≤ q) (hM : 1 / 2 < M)
    (hcenter : a / 2 + b = 1 / 2)
    (hmesh : a * Real.log q < Real.log 2 / (2 * M - 1)) :
    M < (1 - b) / a := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq
  have hscale : a * Real.log 2 < Real.log 2 / (2 * M - 1) :=
    (mul_le_mul_of_nonneg_left hlogq ha.le).trans_lt hmesh
  have hden : 0 < 2 * M - 1 := by linarith only [hM]
  have hprod := (lt_div_iff₀ hden).mp hscale
  have hasmall : a * (2 * M - 1) < 1 := by
    nlinarith only [hprod, hlog]
  rw [lt_div_iff₀ ha]
  nlinarith only [hasmall, hcenter]

end GaloisForLFunctions.ArithmeticResonanceTheory
