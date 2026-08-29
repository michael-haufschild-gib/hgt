import Mathlib

/-!
# Hurwitz transfer of a closed zero constraint

A nonzero entire locally uniform limit inherits every closed geometric constraint satisfied by the
zeros of its approximants.  The existence half is Rouché-free: a perturbation dominating a base
function on a sphere plants a zero of the sum inside the ball, by the maximum principle applied to
the quotient.
-/

open Complex Metric Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Sphere domination plants a zero: if `h` vanishes at the centre, `g` does not, and
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
    · have hfpos : (0 : ℝ) < ‖g z + h z‖ := lt_of_lt_of_le (by linarith) hlow
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

/-- A zero isolated by one sphere persists inside that sphere under locally uniform convergence. -/
theorem eventually_exists_zero_closedBall_of_tendstoLocallyUniformly
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn F atTop)
    (hF : Differentiable ℂ F)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : F z = 0)
    (hsphere : ∀ w ∈ sphere z r, F w ≠ 0) :
    ∀ᶠ n in atTop, ∃ w ∈ closedBall z r, Fn n w = 0 := by
  have hsphereNonempty : (sphere z r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  have hnormContinuous : ContinuousOn (fun w => ‖F w‖) (sphere z r) :=
    hF.continuous.continuousOn.norm
  obtain ⟨w₀, hw₀, hmin⟩ :=
    (isCompact_sphere z r).exists_isMinOn hsphereNonempty hnormContinuous
  have hminPos : 0 < ‖F w₀‖ := norm_pos_iff.mpr (hsphere w₀ hw₀)
  have hconvSphere : TendstoUniformlyOn Fn F atTop (sphere z r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_sphere z r)).mp hconv.tendstoLocallyUniformlyOn
  have hclose : ∀ᶠ n in atTop, ∀ w ∈ sphere z r,
      dist (F w) (Fn n w) < ‖F w₀‖ / 3 :=
    (Metric.tendstoUniformlyOn_iff.mp hconvSphere) (‖F w₀‖ / 3)
      (div_pos hminPos (by norm_num))
  filter_upwards [hFn, hclose] with n hn hcloseN
  by_cases hnz : Fn n z = 0
  · exact ⟨z, mem_closedBall_self hr.le, hnz⟩
  · let g : ℂ → ℂ := fun w => Fn n w - F w
    have hg : Differentiable ℂ g := fun w => (hn w).sub (hF w)
    have hg0 : g z ≠ 0 := by
      simp only [g, hz, sub_zero]
      exact hnz
    have hdom : ∀ w ∈ sphere z r, 3 * ‖g w‖ ≤ ‖F w‖ := by
      intro w hw
      have hcloseW := hcloseN w hw
      have hminW := hmin hw
      change ‖F w₀‖ ≤ ‖F w‖ at hminW
      have hnorm : ‖g w‖ = dist (F w) (Fn n w) := by
        simp only [g, dist_eq_norm]
        rw [norm_sub_rev]
      rw [hnorm]
      nlinarith
    obtain ⟨w, hw, hwzero⟩ := exists_zero_of_sphere_domination hr
      hg.diffContOnCl hF.diffContOnCl hz hg0 hdom
    refine ⟨w, hw, ?_⟩
    simpa only [g, sub_add_cancel] using hwzero

/-- **Hurwitz closed-locus transfer.** The zero set of a nonzero entire locally uniform limit stays
inside every closed set that contains all zeros of the approximants. -/
theorem zero_mem_closed_of_tendstoLocallyUniformly
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ} {S : Set ℂ}
    (hconv : TendstoLocallyUniformly Fn F atTop)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hS : IsClosed S)
    (hzeroS : ∀ᶠ n in atTop, ∀ w, Fn n w = 0 → w ∈ S)
    {a z : ℂ} (ha : F a ≠ 0) (hz : F z = 0) : z ∈ S := by
  rw [← hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 z, F w = 0 := by
    intro hev
    have hall := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ a)
    exact ha hall
  have hpunct : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 :=
    (hF z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hnotEventuallyZero
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  let r : ℝ := min (ε / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
  have hsphere : ∀ w ∈ sphere z r, F w ≠ 0 := by
    intro w hw
    apply hδsub
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hrδ)
    · exact Set.mem_compl_singleton_iff.mpr
        (Metric.ne_of_mem_sphere hw hr.ne')
  have hlocal := eventually_exists_zero_closedBall_of_tendstoLocallyUniformly
    hconv (fun w => (hF w (Set.mem_univ w)).differentiableAt) hFn hr hz hsphere
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlocal
  obtain ⟨M, hM⟩ := eventually_atTop.1 hzeroS
  obtain ⟨w, hwball, hwzero⟩ := hN (max N M) (le_max_left _ _)
  refine ⟨w, hM (max N M) (le_max_right _ _) w hwzero, ?_⟩
  have hdist : dist z w ≤ r := by
    simpa [dist_comm] using Metric.mem_closedBall.mp hwball
  exact hdist.trans_lt hrε

end GaloisForLFunctions.HTGeometry
