import GaloisForLFunctions.HTGeometry.ResidueJumpLowerBound

/-!
# A residue is a genuine singularity, and is not a uniform limit

The residue jump bound says a non-zero residue keeps a function uniformly away
from every function with vanishing circle integral.  Two consequences complete
that mechanism.

First, a non-vanishing circle integral certifies non-analyticity outright: by
Cauchy's theorem an analytic function on the closed disk integrates to zero
around it.  This is the certificate consumed by the radius-versus-singularity
argument.

Second, a function with non-zero residue is not the uniform limit, on the
circle, of any family of functions with vanishing circle integral.  This is the
qualitative form of the jump: the residue-carrying member of a parametrised
family is isolated from the residue-free members, so the family cannot be
continuous at that parameter.
-/

open Complex Filter Metric Topology

namespace HTGeometry

/-- **Cauchy certificate for a genuine singularity.**  A non-vanishing circle
integral certifies that the function is not analytic on the closed disk. -/
theorem not_analyticOnNhd_of_circleIntegral_ne_zero {g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hne : (∮ z in C(c, r), g z) ≠ 0) :
    ¬ AnalyticOnNhd ℂ g (Metric.closedBall c r) := by
  intro hg
  refine hne ?_
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    Set.countable_empty hg.continuousOn fun z hz => ?_
  exact (hg z (Metric.ball_subset_closedBall hz.1)).differentiableAt

/-- **A residue is not a uniform limit of residue-free functions.**  If every
member of a family has vanishing circle integral, the family cannot converge
uniformly on that circle to a function with non-zero residue. -/
theorem not_tendstoUniformlyOn_of_residue_ne_zero {ι : Type*} {l : Filter ι}
    [l.NeBot] {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {c ρ : ℂ} {r : ℝ} (hr : 0 < r)
    (hρ : ρ ≠ 0)
    (hF : ∀ i, CircleIntegrable (F i) c r) (hg : CircleIntegrable g c r)
    (hFint : ∀ i, (∮ z in C(c, r), F i z) = 0)
    (hres : (∮ z in C(c, r), g z) = 2 * Real.pi * Complex.I * ρ) :
    ¬ TendstoUniformlyOn F g l (Metric.sphere c r) := by
  intro huc
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hε : 0 < ‖ρ‖ / (2 * r) := by positivity
  obtain ⟨i, hi⟩ := (Metric.tendstoUniformlyOn_iff.mp huc _ hε).exists
  have hC : ∀ z ∈ Metric.sphere c r, ‖g z - F i z‖ ≤ ‖ρ‖ / (2 * r) := by
    intro z hz
    have h := hi z hz
    rw [dist_eq_norm] at h
    exact h.le
  have hbound :=
    residue_jump_of_integral_eq_zero hr (hF i) hg (hFint i) hres hC
  have hlt : ‖ρ‖ / (2 * r) < ‖ρ‖ / r := by
    apply div_lt_div_of_pos_left hρpos hr
    linarith
  linarith

end HTGeometry
