import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A logarithm falls short of every positive slope

The logarithm is below twice the square root, because halving it puts it below the square root's own
logarithm bound.  A square root is eventually below any positive multiple of the argument, so a
logarithm plus any constant is eventually below any positive slope times the argument, less any
constant.

This is the comparison a linear lower bound needs against a logarithmic cap.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology

/-- **The logarithm is below twice the root.** -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have hpow : Real.log (Real.sqrt x ^ 2) = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [← hpow, hsq]
  have hbound : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hspos
  rw [hlog]
  linarith

/-- **A logarithm plus a constant is eventually below any positive slope.** -/
theorem eventually_log_add_le_linear {s : ℝ} (hs : 0 < s) (C δ : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.log x + δ ≤ s * x - C := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (16 / s ^ 2), eventually_ge_atTop (2 * (C + δ) / s)] with x hx h1 h2
  have hy : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hynn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  -- the root is at least four over the slope
  have hy4 : 4 / s ≤ Real.sqrt x := by
    by_contra hcon
    push Not at hcon
    have h4 : (0 : ℝ) < 4 / s := by positivity
    have hlt : Real.sqrt x ^ 2 < (4 / s) ^ 2 := by nlinarith [hynn, hcon]
    rw [hy] at hlt
    have h16 : (4 / s) ^ 2 = 16 / s ^ 2 := by
      field_simp
      norm_num
    rw [h16] at hlt
    linarith
  have h4s : 4 ≤ Real.sqrt x * s := (div_le_iff₀ hs).mp hy4
  have hroot : 2 * Real.sqrt x ≤ s * x / 2 := by
    nlinarith [hy, hynn, h4s]
  have hshift : C + δ ≤ s * x / 2 := by
    rw [div_le_iff₀ hs] at h2
    linarith
  have hlog := log_le_two_mul_sqrt hx
  linarith

/-- **Any sublinear growth is eventually below any positive slope.**  The logarithm is one case;
what the argument uses is only that the quotient by the argument tends to zero. -/
theorem eventually_sublinear_add_le_linear {f : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hf : Tendsto (fun r : ℝ => f r / r) atTop (𝓝 0)) (C δ : ℝ) :
    ∀ᶠ r : ℝ in atTop, f r + δ ≤ s * r - C := by
  have hhalf : ∀ᶠ r : ℝ in atTop, f r / r < s / 2 :=
    hf.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < s / 2))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hhalf,
    eventually_ge_atTop (2 * (C + δ) / s)] with r hr hquot hbig
  have hfr : f r < s / 2 * r := by
    rw [div_lt_iff₀ hr] at hquot
    linarith
  have hshift : C + δ ≤ s * r / 2 := by
    rw [div_le_iff₀ hs] at hbig
    linarith
  linarith

end GaloisForLFunctions.HTGeometry
