import GaloisForLFunctions.RHTower.PerturbationZero
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Closed zero-locus transfer under locally uniform convergence

A nonzero entire locally uniform limit inherits every closed geometric constraint satisfied by the
zeros of the approximants.  The proof supplies the missing Hurwitz-style existence step from the
project's sphere-domination theorem, rather than assuming sequences of approximating zeros.

The `XiC` specialization makes the live determinant route explicit: entire approximants with real
zeros that converge locally uniformly to `XiC` imply the Riemann hypothesis.
-/

open Complex Metric Set Filter Topology

namespace RHTower

/-- A zero isolated by one sphere persists inside that sphere under locally uniform convergence.
This is the local Hurwitz existence mechanism used by the closed-locus transfer theorem. -/
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

/-- The zero set of a nonzero entire locally uniform limit stays inside every closed set that
contains all zeros of the approximants. -/
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

/-- A locally uniform entire approximation of `XiC` by functions whose zeros are real proves RH.
The approximants need not be polynomials; self-adjoint characteristic determinants are the main
application. -/
theorem riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants
    {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hreal : ∀ᶠ n in atTop, ∀ z, Fn n z = 0 → z.im = 0) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have him : z.im = 0 := zero_mem_closed_of_tendstoLocallyUniformly
    hconv XiC_analytic hFn
    (isClosed_eq Complex.continuous_im continuous_const)
    hreal XiC_zero_ne hXiC
  have hzIm : z.im = 1 / 2 - ρ.re := by
    simp [z]
  have hre : ρ.re = 1 / 2 := by linarith [him, hzIm]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) hre

end RHTower
