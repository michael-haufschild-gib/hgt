import Mathlib

/-!
# Integration by parts with interior derivatives

The standard integration-by-parts formula asks for derivatives on the closed interval.  That is too
strong when one factor degenerates at an endpoint: a weight can be differentiable throughout the
open interval, bounded, and still have no derivative — or even no defined value — at the endpoint,
while the *product* being differentiated is perfectly continuous there because the other factor
vanishes.

The fundamental theorem in its one-sided form covers exactly that situation, so integration by parts
does too.  The companion lemma supplies the integrability such a weight has automatically: bounded
and continuous on the open interval is enough, since the endpoints are null.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- A function continuous and bounded on the open interval is interval integrable: the endpoints
carry no measure. -/
theorem intervalIntegrable_of_continuousOn_Ioo_of_bounded {f : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Ioo a b)) (hM : ∀ x ∈ Ioo a b, |f x| ≤ M) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hfin : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    ⟨by simp⟩
  have hIoo : IntegrableOn f (Ioo a b) volume := by
    refine ⟨hf.aestronglyMeasurable measurableSet_Ioo, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := M) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    simp [Real.norm_eq_abs, hM x hx]
  exact hIoo.congr_set_ae (Ioo_ae_eq_Ioc).symm

/-- **Integration by parts with derivatives only on the interior.**  Only the product has to be
continuous up to the endpoints. -/
theorem integral_mul_deriv_eq_deriv_mul_interior {a b : ℝ} (hab : a ≤ b) {u v u' v' : ℝ → ℝ}
    (hcont : ContinuousOn (fun x : ℝ => u x * v x) (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hi1 : IntervalIntegrable (fun x : ℝ => u' x * v x) volume a b)
    (hi2 : IntervalIntegrable (fun x : ℝ => u x * v' x) volume a b) :
    (∫ x in a..b, u x * v' x) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  have hderiv : ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun t : ℝ => u t * v t) (u' x * v x + u x * v' x) (Ioi x) x :=
    fun x hx => ((hu x hx).mul (hv x hx)).hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at h
  linarith [h]

/-- Continuity at a degenerate endpoint: a bounded factor against a factor vanishing there. -/
theorem continuousWithinAt_mul_of_bounded_of_tendsto_zero {u v : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hM : ∀ x ∈ Ioc a b, |u x| ≤ M) (hv : Continuous v) (hv0 : v a = 0) :
    ContinuousWithinAt (fun x : ℝ => u x * v x) (Icc a b) a := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (u b)) (hM b ⟨hab, le_rfl⟩)
  have hzero : u a * v a = 0 := by simp [hv0]
  rw [ContinuousWithinAt, hzero]
  have hvt : Filter.Tendsto (fun x : ℝ => M * |v x|) (nhdsWithin a (Icc a b)) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => M * |v x|) a := (hv.abs.const_mul M).continuousAt
    have h := hc.continuousWithinAt (s := Icc a b)
    rw [ContinuousWithinAt, hv0] at h
    simpa using h
  refine squeeze_zero_norm' ?_ hvt
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h, hv0]
    simp
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM x ⟨h, hx.2⟩) (abs_nonneg _)

end GaloisForLFunctions.HTGeometry
