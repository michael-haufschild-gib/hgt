/-
The Rouché-free zero-planting lemma (MWM lane; 11-recurrence-degrees.md §2 step 3).

If a perturbation h dominates a base g on a sphere (‖h‖ ≥ 3‖g‖ there), vanishes at the
center while g does not, then g + h has a zero in the closed ball. Proof: otherwise
F = g/(g+h) is DiffContOnCl on the ball with boundary norm ≤ 1/2 (on the sphere
‖g+h‖ ≥ ‖h‖ − ‖g‖ ≥ 2‖g‖), so the maximum principle caps ‖F(s₀)‖ by 1/2 — but
F(s₀) = g(s₀)/(g(s₀) + 0) = 1. No argument principle, no Rouché (mathlib has neither).

This is the existence engine of the Weyl counterexample: the droves dichotomy fails at
Weyl/Besicovitch regularity because a gaussian-null bump h can plant a lone off-line zero
into an FE-symmetric base. The lemma is generic and reusable for any such surgery.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RiemannTower

namespace RHTower

/-- Sphere domination plants a zero: if `h` vanishes at the center, `g` does not, and
`3‖g‖ ≤ ‖h‖` on the sphere, then `g + h` vanishes somewhere in the closed ball. -/
theorem exists_zero_of_sphere_domination {g h : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (Metric.ball s₀ r)) (hh : DiffContOnCl ℂ h (Metric.ball s₀ r))
    (hcenter : h s₀ = 0) (hg0 : g s₀ ≠ 0)
    (hdom : ∀ z ∈ Metric.sphere s₀ r, 3 * ‖g z‖ ≤ ‖h z‖) :
    ∃ z ∈ Metric.closedBall s₀ r, g z + h z = 0 := by
  by_contra hno
  push Not at hno
  have hne : ∀ z ∈ Metric.closedBall s₀ r, g z + h z ≠ 0 := hno
  have hgc : ContinuousOn g (Metric.closedBall s₀ r) := by
    have := hg.continuousOn; rwa [closure_ball s₀ hr.ne'] at this
  have hfc : ContinuousOn (fun z => g z + h z) (Metric.closedBall s₀ r) := by
    have := hg.continuousOn.add hh.continuousOn
    rwa [closure_ball s₀ hr.ne'] at this
  have hfd : DifferentiableOn ℂ (fun z => g z + h z) (Metric.ball s₀ r) :=
    hg.differentiableOn.add hh.differentiableOn
  have hFd : DiffContOnCl ℂ (fun z => g z / (g z + h z)) (Metric.ball s₀ r) := by
    constructor
    · exact hg.differentiableOn.div hfd
        (fun z hz => hne z (Metric.ball_subset_closedBall hz))
    · rw [closure_ball s₀ hr.ne']
      exact hgc.div hfc hne
  have hbound : ∀ z ∈ frontier (Metric.ball s₀ r), ‖g z / (g z + h z)‖ ≤ 1 / 2 := by
    intro z hz
    rw [frontier_ball s₀ hr.ne'] at hz
    have h3 : 3 * ‖g z‖ ≤ ‖h z‖ := hdom z hz
    have hlow : 2 * ‖g z‖ ≤ ‖g z + h z‖ := by
      have hsub : ‖h z‖ - ‖-(g z)‖ ≤ ‖h z - -(g z)‖ := norm_sub_norm_le _ _
      rw [norm_neg, sub_neg_eq_add, add_comm] at hsub
      linarith
    rw [norm_div]
    rcases eq_or_lt_of_le (norm_nonneg (g z)) with hgz0 | hgz0
    · rw [← hgz0, zero_div]
      norm_num
    · have hfpos : (0:ℝ) < ‖g z + h z‖ := lt_of_lt_of_le (by linarith) hlow
      rw [div_le_iff₀ hfpos]
      linarith
  have hs₀cl : s₀ ∈ closure (Metric.ball s₀ r) := by
    rw [closure_ball s₀ hr.ne']
    exact Metric.mem_closedBall_self hr.le
  have hcen := Complex.norm_le_of_forall_mem_frontier_norm_le
    Metric.isBounded_ball hFd hbound hs₀cl
  have hone : g s₀ / (g s₀ + h s₀) = 1 := by
    rw [hcenter, add_zero, div_self hg0]
  simp only [hone] at hcen
  norm_num at hcen

end RHTower

namespace RHTower

/-- A sphere-domination zero planted inside the right half-plane contradicts RH
when the perturbed carrier is ξ on the closed ball. -/
theorem not_riemannHypothesis_of_sphere_domination_right {g h : ℂ → ℂ} {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.closedBall s₀ r ⊆ rightHalf)
    (hg : DiffContOnCl ℂ g (Metric.ball s₀ r))
    (hh : DiffContOnCl ℂ h (Metric.ball s₀ r))
    (hcenter : h s₀ = 0) (hg0 : g s₀ ≠ 0)
    (hdom : ∀ z ∈ Metric.sphere s₀ r, 3 * ‖g z‖ ≤ ‖h z‖)
    (hxi : ∀ z ∈ Metric.closedBall s₀ r, xi z = g z + h z) :
    ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨z, hz, hzero⟩ := exists_zero_of_sphere_domination hr hg hh hcenter hg0 hdom
  exact (rh_iff_xi_ne_zero_right.mp hRH z (hball hz)) (by rw [hxi z hz, hzero])

end RHTower

namespace RHTower

/-- A sphere-domination zero planted in a ball whose radius is smaller than the
right-half margin of its center contradicts RH. -/
theorem not_riemannHypothesis_of_sphere_domination_center_margin {g h : ℂ → ℂ}
    {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hmargin : 1 / 2 + r < s₀.re)
    (hg : DiffContOnCl ℂ g (Metric.ball s₀ r))
    (hh : DiffContOnCl ℂ h (Metric.ball s₀ r))
    (hcenter : h s₀ = 0) (hg0 : g s₀ ≠ 0)
    (hdom : ∀ z ∈ Metric.sphere s₀ r, 3 * ‖g z‖ ≤ ‖h z‖)
    (hxi : ∀ z ∈ Metric.closedBall s₀ r, xi z = g z + h z) :
    ¬ RiemannHypothesis := by
  refine not_riemannHypothesis_of_sphere_domination_right hr ?_ hg hh hcenter hg0 hdom hxi
  intro z hz
  rw [mem_rightHalf]
  have hzdist : dist z s₀ ≤ r := by simpa [Metric.mem_closedBall] using hz
  have hznorm : ‖z - s₀‖ ≤ r := by simpa [Complex.dist_eq] using hzdist
  have hproj : s₀.re ≤ z.re + ‖z - s₀‖ := by
    simpa [Complex.sub_re] using (abs_le.mp (Complex.abs_re_le_norm (z - s₀))).1
  linarith

end RHTower
