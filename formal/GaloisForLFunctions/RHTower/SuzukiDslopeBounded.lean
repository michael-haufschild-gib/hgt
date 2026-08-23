import GaloisForLFunctions.RHTower.SuzukiHalfInnerLocalFactor

noncomputable section

/-!
# Boundedness of the divided slope on the closed upper half-plane

Suzuki's family `F_γ` is a constant multiple of `dslope (A/E) γ`.  Two bounds are recorded here,
both consequences of `‖A/E‖ ≤ 1` on the closed upper half-plane: the reciprocal-distance bound
`‖dslope (A/E) γ z‖ ≤ 1/‖z - γ‖` away from `γ`, and a uniform bound, obtained by combining that
with continuity on the compact part of the half-plane within distance one of `γ`.

Together they give `‖F_γ‖ ≤ min (C, 1/‖z-γ‖)`, which is what makes the mass of `F_γ` on the
horizontal lines uniformly bounded — the hypothesis of the analytic Hardy-space predicate.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- Away from the zero the divided slope inherits the contraction bound. -/
theorem norm_dslope_suzukiHalfInner_le_of_one_le (hRH : RiemannHypothesis) {γ : ℂ}
    (hγ : XiC γ = 0) {z : ℂ} (hz : 0 ≤ z.im) (h1 : 1 ≤ ‖z - γ‖) :
    ‖dslope suzukiHalfInner γ z‖ ≤ 1 := by
  have hne : z ≠ γ := by
    intro h
    rw [h, sub_self, norm_zero] at h1
    linarith
  rw [dslope_suzukiHalfInner_apply hγ hne, norm_div]
  have hnum := norm_suzukiHalfInner_le_one_of_rh hRH hz
  have hden : (0 : ℝ) < ‖z - γ‖ := by linarith
  rw [div_le_one hden]
  linarith

/-- **The divided slope of `A/E` is bounded on the closed upper half-plane.** -/
theorem exists_bound_dslope_suzukiHalfInner (hRH : RiemannHypothesis) {γ : ℂ}
    (hγ : XiC γ = 0) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖dslope suzukiHalfInner γ z‖ ≤ C := by
  set K : Set ℂ := {z : ℂ | 0 ≤ z.im} ∩ Metric.closedBall γ 1 with hK
  have hKcomp : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const Complex.continuous_im).inter Metric.isClosed_closedBall
    · exact Metric.isBounded_closedBall.subset Set.inter_subset_right
  have hcont : ContinuousOn (dslope suzukiHalfInner γ) K := fun z hz =>
    (differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ hz.1).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hKcomp.exists_bound_of_continuousOn hcont
  refine ⟨max M 1, fun z hz => ?_⟩
  rcases le_or_gt 1 ‖z - γ‖ with h | h
  · exact le_trans (norm_dslope_suzukiHalfInner_le_of_one_le hRH hγ hz h) (le_max_right _ _)
  · have hmem : z ∈ K := ⟨hz, by simpa [Metric.mem_closedBall, dist_eq_norm] using h.le⟩
    exact le_trans (hM z hmem) (le_max_left _ _)

/-- The divided slope also inherits the reciprocal-distance bound. -/
theorem norm_dslope_suzukiHalfInner_le_inv (hRH : RiemannHypothesis) {γ : ℂ}
    (hγ : XiC γ = 0) {z : ℂ} (hz : 0 ≤ z.im) (hne : z ≠ γ) :
    ‖dslope suzukiHalfInner γ z‖ ≤ 1 / ‖z - γ‖ := by
  rw [dslope_suzukiHalfInner_apply hγ hne, norm_div]
  have hden : (0 : ℝ) < ‖z - γ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [div_le_div_iff_of_pos_right hden]
  exact norm_suzukiHalfInner_le_one_of_rh hRH hz


end RHTower
