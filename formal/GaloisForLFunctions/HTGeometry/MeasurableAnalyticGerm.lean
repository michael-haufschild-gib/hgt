import GaloisForLFunctions.Bottcher.InverseBranchPeriodic
import GaloisForLFunctions.HTGeometry.ImplicitLipschitzGraph

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every analytic germ has a globally measurable representative agreeing on a neighborhood. -/
theorem exists_measurable_eventuallyEq_of_analyticAt
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    ∃ g : ℂ → ℂ, Measurable g ∧ AnalyticAt ℂ g a ∧ f =ᶠ[nhds a] g := by
  let K : NNReal := ⟨‖deriv f a‖ + 1, by positivity⟩
  have hK : ‖deriv f a‖ < (K : ℝ) := by
    change ‖deriv f a‖ < ‖deriv f a‖ + 1
    linarith
  obtain ⟨r, hr, hball⟩ :=
    Bottcher.exists_closedBall_deriv_bound_of_analyticAt hf hK
  have hlip : LipschitzOnWith K f (closedBall a r) := by
    apply (convex_closedBall a r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    · intro z hz
      exact (hball z hz).1.hasDerivWithinAt
    · intro z hz
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hball z hz).2
  obtain ⟨g, hgLip, hfg⟩ :=
    GaloisForLFunctions.LipschitzOnWith.extend_complex hlip
  have hev : f =ᶠ[nhds a] g := by
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact hfg (mem_closedBall.mpr (mem_ball.mp hz).le)
  refine ⟨g, hgLip.continuous.measurable, ?_, hev⟩
  exact hf.congr hev

/-- An analytic germ admits a smaller closed ball carrying the uniform analyticity, derivative,
and Lipschitz data required by weighted arc gluing. -/
theorem exists_closedBall_analytic_lipschitz_data_of_analyticAt
    {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hf : AnalyticAt ℂ f a) (hR : 0 < R) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧ 3 * r < R ∧
      (∀ z ∈ closedBall a (3 * r), AnalyticAt ℂ f z) ∧
      (∀ x ∈ closedBall a (3 * r), ∀ y ∈ closedBall a (3 * r),
        ‖f y - f x‖ ≤ C * ‖y - x‖) ∧
      (∀ z ∈ closedBall a (3 * r), ‖deriv f z‖ ≤ C) := by
  let K : NNReal := ⟨‖deriv f a‖ + 1, by positivity⟩
  have hK : ‖deriv f a‖ < (K : ℝ) := by
    change ‖deriv f a‖ < ‖deriv f a‖ + 1
    linarith
  obtain ⟨rd, hrd, hderivBall⟩ :=
    Bottcher.exists_closedBall_deriv_bound_of_analyticAt hf hK
  have hdiffEventually : ∀ᶠ z in nhds a, DifferentiableAt ℂ f z :=
    Complex.analyticAt_iff_eventually_differentiableAt.mp hf
  obtain ⟨ra, hra, hdiffBall⟩ := Metric.mem_nhds_iff.mp hdiffEventually
  let s := min R (min rd ra)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  let r := s / 4
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have h3rS : 3 * r < s := by
    dsimp [r]
    linarith
  have h3rR : 3 * r < R := h3rS.trans_le (min_le_left _ _)
  have h3rrd : 3 * r < rd :=
    h3rS.trans_le ((min_le_right R (min rd ra)).trans (min_le_left rd ra))
  have h3rra : 3 * r < ra :=
    h3rS.trans_le ((min_le_right R (min rd ra)).trans (min_le_right rd ra))
  have hderiv (z : ℂ) (hz : z ∈ closedBall a (3 * r)) :
      HasDerivAt f (deriv f z) z ∧ ‖deriv f z‖ ≤ (K : ℝ) := by
    apply hderivBall z
    rw [mem_closedBall] at hz ⊢
    exact hz.trans (le_of_lt h3rrd)
  have hanalytic (z : ℂ) (hz : z ∈ closedBall a (3 * r)) :
      AnalyticAt ℂ f z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hzra : dist z a < ra := by
      rw [mem_closedBall] at hz
      exact hz.trans_lt h3rra
    let ε := (ra - dist z a) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    filter_upwards [ball_mem_nhds z hε] with w hw
    apply hdiffBall
    rw [mem_ball] at hw ⊢
    have htri := dist_triangle w z a
    dsimp [ε] at hw
    linarith
  have hlip : LipschitzOnWith K f (closedBall a (3 * r)) := by
    apply (convex_closedBall a (3 * r)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    · intro z hz
      exact (hderiv z hz).1.hasDerivWithinAt
    · intro z hz
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hderiv z hz).2
  refine ⟨r, (K : ℝ), hr, NNReal.coe_nonneg K, h3rR,
    hanalytic, ?_, fun z hz => (hderiv z hz).2⟩
  intro x hx y hy
  simpa [dist_eq, norm_sub_rev] using hlip.dist_le_mul y hy x hx

end

end GaloisForLFunctions.HTGeometry
