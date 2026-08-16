import GaloisForLFunctions.HTGeometry.GermReducedFraction

/-!
# Associated germs have boundedly comparable representatives

A germ that is a unit has a representative bounded away from zero and from infinity on a small
ball, simply by continuity.  Consequently two associated germs have representatives whose ratio is
bounded both ways near the point.

This is the analytic form of the uniqueness of a reduced presentation: two locally reduced
denominators of the same meromorphic function are associated, hence boundedly comparable — the
comparison constant a Siegel-type count needs on the overlaps of a cover, and exactly what a global
entire presentation fails to provide.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **An analytic function is bounded near a point.** -/
theorem exists_norm_bound_of_analyticAt {p : E} {U : E → ℂ} (hU : AnalyticAt ℂ U p) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ w ∈ ball p r, ‖U w‖ ≤ C := by
  have hcont : ContinuousAt U p := hU.continuousAt
  have hev : ∀ᶠ w in 𝓝 p, ‖U w‖ < ‖U p‖ + 1 := by
    have hball : Metric.ball (U p) 1 ∈ 𝓝 (U p) := Metric.ball_mem_nhds _ one_pos
    filter_upwards [hcont.eventually hball] with w hw
    rw [dist_eq_norm] at hw
    calc ‖U w‖ = ‖U p + (U w - U p)‖ := by ring_nf
      _ ≤ ‖U p‖ + ‖U w - U p‖ := norm_add_le _ _
      _ < ‖U p‖ + 1 := by linarith
  obtain ⟨r, hr, hrspec⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, ‖U p‖ + 1, hr, by positivity, ?_⟩
  intro w hw
  exact (hrspec (mem_ball.mp hw)).le

/-- **An analytic function that does not vanish at a point is bounded below near it.** -/
theorem exists_norm_lower_bound_of_ne_zero {p : E} {U : E → ℂ} (hU : AnalyticAt ℂ U p)
    (hne : U p ≠ 0) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ w ∈ ball p r, c ≤ ‖U w‖ := by
  have hcont : ContinuousAt U p := hU.continuousAt
  have hpos : 0 < ‖U p‖ := norm_pos_iff.mpr hne
  have hev : ∀ᶠ w in 𝓝 p, ‖U p‖ / 2 ≤ ‖U w‖ := by
    have hball : Metric.ball (U p) (‖U p‖ / 2) ∈ 𝓝 (U p) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hcont.eventually hball] with w hw
    rw [dist_eq_norm] at hw
    have hsub : ‖U p‖ - ‖U w‖ ≤ ‖U p - U w‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at hsub
    linarith
  obtain ⟨r, hr, hrspec⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨r, ‖U p‖ / 2, hr, by positivity, fun w hw => hrspec (mem_ball.mp hw)⟩

/-- **A unit germ has a representative bounded away from zero.** -/
theorem exists_lower_bound_of_isUnit {p : E} {U : E → ℂ} (hU : AnalyticAt ℂ U p)
    (hunit : IsUnit (analyticGermOf hU)) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ w ∈ ball p r, c ≤ ‖U w‖ := by
  refine exists_norm_lower_bound_of_ne_zero hU ?_
  have := (isUnit_analyticGerm_iff (analyticGermOf hU)).mp hunit
  rwa [analyticGermValue_of hU] at this

/-- **Associated germs have boundedly comparable representatives.** -/
theorem exists_ratio_bound_of_associated {p : E} {B₁ B₂ : E → ℂ}
    (hB₁ : AnalyticAt ℂ B₁ p) (hB₂ : AnalyticAt ℂ B₂ p)
    (hassoc : Associated (analyticGermOf hB₁) (analyticGermOf hB₂)) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ w ∈ ball p r, ‖B₂ w‖ ≤ C * ‖B₁ w‖ := by
  classical
  obtain ⟨v, hv⟩ := hassoc
  obtain ⟨V, hVA, hVeq⟩ := (v : AnalyticGerm p).2
  have hveq : (v : AnalyticGerm p) = analyticGermOf hVA := Subtype.ext hVeq.symm
  obtain ⟨rC, C, hrC, hC, hCspec⟩ := exists_norm_bound_of_analyticAt hVA
  -- the germ identity gives a pointwise identity near `p`
  have hprod : analyticGermOf hB₁ * analyticGermOf hVA = analyticGermOf hB₂ := by
    rw [← hveq]
    exact hv
  have hfun : (fun w => B₁ w * V w) =ᶠ[𝓝 p] B₂ := by
    have hcoe := congrArg (fun x : AnalyticGerm p => (x : Germ (𝓝 p) ℂ)) hprod
    rw [Subring.coe_mul, analyticGermOf_val, analyticGermOf_val, analyticGermOf_val,
      ← Germ.coe_mul] at hcoe
    exact Germ.coe_eq.mp hcoe
  obtain ⟨rE, hrE, hEspec⟩ := Metric.eventually_nhds_iff.mp hfun
  refine ⟨min rC rE, C, lt_min hrC hrE, hC, ?_⟩
  intro w hw
  have hw1 : w ∈ ball p rC := ball_subset_ball (min_le_left _ _) hw
  have hw2 : dist w p < rE := lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _)
  have hval : B₁ w * V w = B₂ w := hEspec hw2
  rw [← hval, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hCspec w hw1) (norm_nonneg _)

end GaloisForLFunctions.HTGeometry
