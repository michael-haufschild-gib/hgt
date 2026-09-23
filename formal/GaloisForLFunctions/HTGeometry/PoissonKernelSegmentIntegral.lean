import Mathlib

/-!
# The segment integral of the shifted Poisson kernel

`v ↦ v/(v² + c²)` is the real part of `(v + ic)⁻¹`, and its primitive is `½log(v²+c²)`.  Over a
segment of length at most six the integral of its absolute value is therefore at most
`log(1 + 9/c²)` — a bound that is `O(1/c²)` for large `|c|` and only logarithmic in `1/|c|` for
small `|c|`.  This is the estimate that controls the contribution of a single zero to the movement
of `log‖xi‖` across a horizontal segment.

## Main results

* `integral_poissonKernelAbs_le`
-/

open MeasureTheory intervalIntegral Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem poissonDenom_pos {c : ℝ} (hc : c ≠ 0) (v : ℝ) : 0 < v ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  have : 0 < c ^ (2 : ℕ) := by positivity
  nlinarith [sq_nonneg v]

theorem hasDerivAt_halfLogDenom {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    HasDerivAt (fun w : ℝ => (1 / 2) * Real.log (w ^ (2 : ℕ) + c ^ (2 : ℕ))) (v / (v ^ (2 : ℕ) + c ^ (2 : ℕ))) v := by
  have hpos := poissonDenom_pos hc v
  have h1 : HasDerivAt (fun w : ℝ => w ^ (2 : ℕ) + c ^ (2 : ℕ)) (2 * v) v := by
    have := (hasDerivAt_pow 2 v).add_const (c ^ (2 : ℕ))
    simpa using this
  have h2 := (h1.log hpos.ne')
  have h3 := h2.const_mul (1 / 2 : ℝ)
  refine h3.congr_deriv ?_
  field_simp

theorem continuous_poissonKernelAbs {c : ℝ} (hc : c ≠ 0) :
    Continuous fun v : ℝ => |v| / (v ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
  refine continuous_abs.div (by fun_prop) fun v => (poissonDenom_pos hc v).ne'

theorem integral_poissonKernel_Icc_right {c : ℝ} (hc : c ≠ 0) :
    (∫ v in (0 : ℝ)..3, v / (v ^ (2 : ℕ) + c ^ (2 : ℕ)))
      = (1 / 2) * Real.log (9 + c ^ (2 : ℕ)) - (1 / 2) * Real.log (c ^ (2 : ℕ)) := by
  have hderiv : ∀ v ∈ uIcc (0 : ℝ) 3,
      HasDerivAt (fun w : ℝ => (1 / 2) * Real.log (w ^ (2 : ℕ) + c ^ (2 : ℕ))) (v / (v ^ (2 : ℕ) + c ^ (2 : ℕ))) v :=
    fun v _ => hasDerivAt_halfLogDenom hc v
  have hint : IntervalIntegrable (fun v : ℝ => v / (v ^ (2 : ℕ) + c ^ (2 : ℕ))) volume 0 3 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_id.div (by fun_prop) fun v => (poissonDenom_pos hc v).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

theorem integral_poissonKernel_Icc_left {c : ℝ} (hc : c ≠ 0) :
    (∫ v in (-3 : ℝ)..0, -(v / (v ^ (2 : ℕ) + c ^ (2 : ℕ))))
      = (1 / 2) * Real.log (9 + c ^ (2 : ℕ)) - (1 / 2) * Real.log (c ^ (2 : ℕ)) := by
  have hderiv : ∀ v ∈ uIcc (-3 : ℝ) 0,
      HasDerivAt (fun w : ℝ => -((1 / 2) * Real.log (w ^ (2 : ℕ) + c ^ (2 : ℕ))))
        (-(v / (v ^ (2 : ℕ) + c ^ (2 : ℕ)))) v :=
    fun v _ => (hasDerivAt_halfLogDenom hc v).neg
  have hint : IntervalIntegrable (fun v : ℝ => -(v / (v ^ (2 : ℕ) + c ^ (2 : ℕ)))) volume (-3) 0 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact (continuous_id.div (by fun_prop) fun v => (poissonDenom_pos hc v).ne').neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num
  ring

theorem integral_poissonKernelAbs_full {c : ℝ} (hc : c ≠ 0) :
    (∫ v in (-3 : ℝ)..3, |v| / (v ^ (2 : ℕ) + c ^ (2 : ℕ))) = Real.log (1 + 9 / c ^ (2 : ℕ)) := by
  have hcont := continuous_poissonKernelAbs hc
  have hsplit : (∫ v in (-3 : ℝ)..3, |v| / (v ^ (2 : ℕ) + c ^ (2 : ℕ)))
      = (∫ v in (-3 : ℝ)..0, |v| / (v ^ (2 : ℕ) + c ^ (2 : ℕ)))
        + ∫ v in (0 : ℝ)..3, |v| / (v ^ (2 : ℕ) + c ^ (2 : ℕ)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hleft : (∫ v in (-3 : ℝ)..0, |v| / (v ^ (2 : ℕ) + c ^ (2 : ℕ)))
      = ∫ v in (-3 : ℝ)..0, -(v / (v ^ (2 : ℕ) + c ^ (2 : ℕ))) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le (by norm_num : (-3 : ℝ) ≤ 0)] at hv
    rw [abs_of_nonpos hv.2]
    ring
  have hright : (∫ v in (0 : ℝ)..3, |v| / (v ^ (2 : ℕ) + c ^ (2 : ℕ)))
      = ∫ v in (0 : ℝ)..3, v / (v ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)] at hv
    rw [abs_of_nonneg hv.1]
  rw [hsplit, hleft, hright, integral_poissonKernel_Icc_left hc,
    integral_poissonKernel_Icc_right hc]
  have hc2 : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
  have hlog : Real.log (1 + 9 / c ^ (2 : ℕ)) = Real.log (9 + c ^ (2 : ℕ)) - Real.log (c ^ (2 : ℕ)) := by
    rw [← Real.log_div (by positivity) hc2.ne']
    congr 1
    field_simp
    ring
  rw [hlog]
  ring

/-- **The segment bound.**  On any subsegment of `[-3,3]` the absolute Poisson kernel integrates to
at most `log(1 + 9/c²)`. -/
theorem integral_poissonKernelAbs_le {c : ℝ} (hc : c ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (ha : -3 ≤ a) (hb : b ≤ 3) :
    (∫ v in a..b, |v| / (v ^ (2 : ℕ) + c ^ (2 : ℕ))) ≤ Real.log (1 + 9 / c ^ (2 : ℕ)) := by
  have hcont := continuous_poissonKernelAbs hc
  rw [← integral_poissonKernelAbs_full hc]
  refine intervalIntegral.integral_mono_interval ha hab hb ?_ (hcont.intervalIntegrable _ _)
  filter_upwards with v
  positivity

end

end GaloisForLFunctions.HTGeometry
