import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Persistence of zeros under uniform approximation

A zero of an entire function `F` that is isolated on a small circle survives uniform
approximation on the closed disc: if `|F| ≥ m₀` on the circle and `|G - F| < m₀/2` on the disc,
the entire function `G` vanishes in the disc. The proof applies the maximum modulus principle to
`1/G`. Every entire function that is not identically zero admits such circles, of arbitrarily
small radius, around every point.
-/
open Metric Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Zeros persist under uniform approximation (Hurwitz, via the maximum modulus principle).**
If `|F| ≥ m₀` on the circle `|z - α| = ρ`, `F(α) = 0`, and an entire `G` satisfies
`|G - F| < m₀/2` on the closed disc, then `G` vanishes somewhere in the closed disc. -/
theorem exists_zero_mem_closedBall_of_norm_sub_lt {F G : ℂ → ℂ} {α : ℂ} {ρ m₀ : ℝ} (hρ : 0 < ρ)
    (hG : Differentiable ℂ G) (hFα : F α = 0) (hsphere : ∀ z ∈ sphere α ρ, m₀ ≤ ‖F z‖)
    (hclose : ∀ z ∈ closedBall α ρ, ‖G z - F z‖ < m₀ / 2) :
    ∃ z ∈ closedBall α ρ, G z = 0 := by
  by_contra hno
  push Not at hno
  have hαmem : α ∈ closedBall α ρ := mem_closedBall_self hρ.le
  have hGα : ‖G α‖ < m₀ / 2 := by simpa [hFα] using hclose α hαmem
  have hm₀ : 0 < m₀ := by linarith [norm_nonneg (G α)]
  have hcl : closure (ball α ρ) = closedBall α ρ := closure_ball α hρ.ne'
  have hdiff : DiffContOnCl ℂ (fun z => (G z)⁻¹) (ball α ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [hcl]
    exact fun z hz => ((hG z).inv (hno z hz)).differentiableWithinAt
  have hbound : ∀ z ∈ frontier (ball α ρ), ‖(G z)⁻¹‖ ≤ 2 / m₀ := by
    intro z hz
    rw [frontier_ball α hρ.ne'] at hz
    have hzc : z ∈ closedBall α ρ := sphere_subset_closedBall hz
    have h1 := hsphere z hz
    have h2 := hclose z hzc
    have h3 : ‖F z‖ ≤ ‖G z‖ + ‖G z - F z‖ := by
      have := norm_sub_le (G z) (G z - F z)
      simpa using this
    have hGz : m₀ / 2 ≤ ‖G z‖ := by linarith
    rw [norm_inv]
    rw [inv_le_comm₀ (by linarith) (by positivity)]
    simpa using hGz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff hbound
    (subset_closure (mem_ball_self hρ))
  rw [norm_inv, inv_le_comm₀ (norm_pos_iff.2 (hno α hαmem)) (by positivity)] at hmax
  have : m₀ / 2 ≤ ‖G α‖ := by simpa using hmax
  linarith

/-- An entire function that is not identically zero is bounded away from zero on some small circle
around any point, of radius below any prescribed bound. -/
theorem exists_sphere_norm_ge_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {w : ℂ} (hw : F w ≠ 0) (α : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ z ∈ sphere α ρ, m₀ ≤ ‖F z‖ := by
  have hA : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  rcases (hA α (mem_univ α)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ α) h
      (mem_univ w)
    exact hw this
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
    set ρ := min ε r / 2
    have hρ : 0 < ρ := by positivity
    have hρε : ρ < ε := by
      have := min_le_left ε r; simp only [ρ]; linarith
    have hρr : ρ < r := by
      have := min_le_right ε r; simp only [ρ]; linarith
    have hne : (sphere α ρ).Nonempty := NormedSpace.sphere_nonempty.2 hρ.le
    obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere α ρ).exists_isMinOn hne
      (hF.continuous.norm.continuousOn)
    have hz₀ne : F z₀ ≠ 0 := by
      have hd : dist z₀ α = ρ := hz₀
      refine hball (by rw [hd]; exact hρε) ?_
      intro hz
      rw [mem_singleton_iff] at hz
      rw [hz, dist_self] at hd
      linarith
    exact ⟨ρ, hρ, hρr, ‖F z₀‖, norm_pos_iff.2 hz₀ne, fun z hz => hmin hz⟩

end GaloisForLFunctions.HTGeometry
