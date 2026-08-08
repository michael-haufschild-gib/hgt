/-
# Hurwitz's theorem: zeros survive a uniform limit

If analytic functions `fₙ` converge uniformly on a closed disc to `f`, and `f` vanishes at the
centre while staying nonzero on the boundary circle, then all but finitely many `fₙ` have a zero
inside the disc.  Mathlib has the Weierstrass convergence theorem but not this.

The proof is the maximum modulus principle applied to `1/fₙ`: if `fₙ` had no zero in the closed
disc, then `‖1/fₙ‖` would be at most its boundary maximum, forcing `‖fₙ(c)‖` to stay away from `0`,
which uniform convergence contradicts.

Main result: `eventually_exists_zero_of_tendstoUniformlyOn`.
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace GaloisForLFunctions.HTGeometry

open Metric Filter Set

/-- The boundary minimum of a continuous nonvanishing function on a circle is positive. -/
theorem exists_pos_le_norm_on_sphere {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (sphere c r)) (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∃ mn : ℝ, 0 < mn ∧ ∀ z ∈ sphere c r, mn ≤ ‖f z‖ := by
  have hcompact : IsCompact (sphere c r) := isCompact_sphere c r
  have hnonempty : (sphere c r).Nonempty := by
    refine ⟨c + r, ?_⟩
    simp [Complex.norm_real, abs_of_pos hr]
  obtain ⟨w, hw, hmin⟩ := hcompact.exists_isMinOn hnonempty hcont.norm
  exact ⟨‖f w‖, norm_pos_iff.mpr (hne w hw), fun z hz => hmin hz⟩

/-- **Hurwitz's theorem, the zero-persistence half.**  A uniform limit of analytic functions on a
closed disc that vanishes at the centre forces all but finitely many of them to vanish somewhere in
the open disc. -/
theorem eventually_exists_zero_of_tendstoUniformlyOn {α : Type*} {p : Filter α}
    {F : α → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ∀ a, DiffContOnCl ℂ (F a) (ball c r))
    (hcont : ContinuousOn f (sphere c r))
    (huniform : TendstoUniformlyOn F f p (closedBall c r))
    (hfc : f c = 0) (hfne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∀ᶠ a in p, ∃ z ∈ ball c r, F a z = 0 := by
  obtain ⟨mn, hmn0, hmn⟩ := exists_pos_le_norm_on_sphere hr hcont hfne
  have hsphere_sub : sphere c r ⊆ closedBall c r := sphere_subset_closedBall
  have hc : c ∈ closedBall c r := mem_closedBall_self hr.le
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  filter_upwards [huniform (mn / 2) (by positivity)] with a ha
  by_contra hno'
  have hno : ∀ z ∈ ball c r, F a z ≠ 0 := fun z hz hzero => hno' ⟨z, hz, hzero⟩
  -- `F a` is nonvanishing on the closed disc
  have hFne : ∀ z ∈ closedBall c r, F a z ≠ 0 := by
    intro z hz hzero
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hlt | heq
    · exact hno z (mem_ball.mpr hlt) hzero
    · have hzs : z ∈ sphere c r := Metric.mem_sphere.mpr heq
      have h1 : mn ≤ ‖f z‖ := hmn z hzs
      have h2 : dist (f z) (F a z) < mn / 2 := ha z (hsphere_sub hzs)
      rw [hzero] at h2
      simp only [dist_zero_right] at h2
      linarith
  -- the boundary bound for `1/F a`
  have hboundary : ∀ z ∈ frontier (ball c r), ‖(F a z)⁻¹‖ ≤ 2 / mn := by
    intro z hz
    rw [frontier_ball c hr.ne'] at hz
    have h1 : mn ≤ ‖f z‖ := hmn z hz
    have h2 : dist (f z) (F a z) < mn / 2 := ha z (hsphere_sub hz)
    have h3 : mn / 2 ≤ ‖F a z‖ := by
      have := norm_sub_norm_le (f z) (F a z)
      rw [← Complex.dist_eq] at this
      linarith
    have h4 : (0 : ℝ) < ‖F a z‖ := lt_of_lt_of_le (by positivity) h3
    rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ h4 hmn0]
    linarith
  -- the maximum modulus principle
  have hdiff : DiffContOnCl ℂ (fun z => (F a z)⁻¹) (ball c r) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      exact ((hF a).differentiableOn z hz).inv (hFne z (ball_subset_closedBall hz))
    · rw [closure_ball c hr.ne']
      exact ContinuousOn.inv₀ (hF a).continuousOn_ball hFne
  have hmax : ‖(F a c)⁻¹‖ ≤ 2 / mn :=
    Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdiff hboundary
      (by rw [closure_ball c hr.ne']; exact hc)
  -- but `‖F a c‖ < mn/2`, so `‖(F a c)⁻¹‖ > 2/mn`
  have hcz : ‖F a c‖ < mn / 2 := by
    have h2 : dist (f c) (F a c) < mn / 2 := ha c hc
    rw [hfc] at h2
    simpa [dist_eq_norm] using h2
  have hFc0 : F a c ≠ 0 := hFne c hc
  rw [norm_inv] at hmax
  have hpos : 0 < ‖F a c‖ := norm_pos_iff.mpr hFc0
  rw [inv_eq_one_div, div_le_div_iff₀ hpos hmn0] at hmax
  linarith

end GaloisForLFunctions.HTGeometry
