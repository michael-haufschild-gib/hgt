import GaloisForLFunctions.RHTower.SoninRefTailPolynomialDecay

/-!
# The majorant beats every weight

The reference majorant is below a constant over any power of the band radius, so multiplying it by a
fixed power — or by a root — still gives something vanishing: one extra order of decay absorbs the
weight and leaves a constant over the radius.

This is what the schedule needs, since its middle slack term is the majorant at a radius times the
root of that radius.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- **Every power weight is absorbed.** -/
theorem tendsto_pow_mul_soninRefTailSup_atTop (n : ℕ) :
    Tendsto (fun u : ℝ => u ^ n * soninRefTailSup u) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_soninRefTailSup_le_div (n + 1)
  refine squeeze_zero' ?_ ?_ (Filter.Tendsto.const_div_atTop tendsto_id C)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have := soninRefTailSup_nonneg u
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hbound := hC u hu
    have hupow : (0 : ℝ) < u ^ n := by positivity
    have hupow1 : (0 : ℝ) < u ^ (n + 1) := by positivity
    calc u ^ n * soninRefTailSup u ≤ u ^ n * (C / u ^ (n + 1)) := by
          exact mul_le_mul_of_nonneg_left hbound hupow.le
      _ = C / u := by
          rw [pow_succ]
          field_simp

/-- **The root weight is absorbed.**  The majorant times the root of the radius vanishes. -/
theorem tendsto_sqrt_mul_soninRefTailSup_atTop :
    Tendsto (fun u : ℝ => Real.sqrt u * soninRefTailSup u) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_soninRefTailSup_le_div 2
  refine squeeze_zero' ?_ ?_ (Filter.Tendsto.const_div_atTop tendsto_id C)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have h1 := soninRefTailSup_nonneg u
    have h2 : (0 : ℝ) ≤ Real.sqrt u := Real.sqrt_nonneg u
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hbound := hC u hu0
    have hs1 : (1 : ℝ) ≤ Real.sqrt u := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hu
    have hsle : Real.sqrt u ≤ u := by
      nlinarith [Real.sq_sqrt hu0.le, hs1]
    calc Real.sqrt u * soninRefTailSup u ≤ Real.sqrt u * (C / u ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg u)
      _ ≤ u * (C / u ^ (2 : ℕ)) := mul_le_mul_of_nonneg_right hsle (by positivity)
      _ = C / u := by
          rw [pow_two]
          field_simp

end RHTower
