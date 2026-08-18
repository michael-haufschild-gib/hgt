import GaloisForLFunctions.RHTower.SuzukiCharacteristicEntireLimitNoGo
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# The corrected meromorphic reading of Suzuki's characteristic limit

Suzuki's displayed limit target `z² ξ(1/2-iz)/ξ'(1/2-iz)` has poles: at a critical point of the
centered completed function where the function itself does not vanish, the quotient blows up, and
the polynomial prefactor cannot cancel it away from the origin.  Two distinct positive real zeros
of the centered function produce such a point by Rolle's theorem, so the ordinary entire-compact
convergence is impossible.

The meaningful repair is locally uniform convergence on compacta avoiding the pole set.  This
module states that corrected wall and proves that it still implies the Riemann hypothesis: an
off-real zero of the centered completed function is a zero — never a pole — of the quotient, so a
Hurwitz argument in a small pole-free disc would force non-real zeros of the real-zero
characteristic functions.

The Hurwitz existence step is supplied on an arbitrary open set, generalizing the entire-case
transfer of `LocallyUniformZeroTransfer`.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Hurwitz existence on an open set -/

/-- **Local Hurwitz existence on an open set.**  A zero of the limit isolated by one sphere inside
the open set persists inside that sphere for the approximants. -/
theorem eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ} {Ω : Set ℂ}
    (hconv : TendstoLocallyUniformlyOn Fn F atTop Ω)
    (hF : AnalyticOnNhd ℂ F Ω)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall z r ⊆ Ω) (hz : F z = 0)
    (hsphere : ∀ w ∈ sphere z r, F w ≠ 0) :
    ∀ᶠ n in atTop, ∃ w ∈ closedBall z r, Fn n w = 0 := by
  have hFcont : ContinuousOn F (closedBall z r) := fun w hw =>
    ((hF w (hball hw)).continuousAt).continuousWithinAt
  have hFdiff : DifferentiableOn ℂ F (ball z r) := fun w hw =>
    ((hF w (hball (ball_subset_closedBall hw))).differentiableAt).differentiableWithinAt
  have hFcl : DiffContOnCl ℂ F (ball z r) := by
    refine ⟨hFdiff, ?_⟩
    rw [closure_ball z hr.ne']
    exact hFcont
  have hsphereNonempty : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hnormContinuous : ContinuousOn (fun w => ‖F w‖) (sphere z r) :=
    (hFcont.mono sphere_subset_closedBall).norm
  obtain ⟨w₀, hw₀, hmin⟩ :=
    (isCompact_sphere z r).exists_isMinOn hsphereNonempty hnormContinuous
  have hminPos : 0 < ‖F w₀‖ := norm_pos_iff.mpr (hsphere w₀ hw₀)
  have hconvSphere : TendstoUniformlyOn Fn F atTop (sphere z r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z r)).mp
      (hconv.mono (le_trans sphere_subset_closedBall hball))
  have hclose : ∀ᶠ n in atTop, ∀ w ∈ sphere z r,
      dist (F w) (Fn n w) < ‖F w₀‖ / 3 :=
    (Metric.tendstoUniformlyOn_iff.mp hconvSphere) (‖F w₀‖ / 3)
      (div_pos hminPos (by norm_num))
  filter_upwards [hFn, hclose] with n hn hcloseN
  by_cases hnz : Fn n z = 0
  · exact ⟨z, mem_closedBall_self hr.le, hnz⟩
  · let g : ℂ → ℂ := fun w => Fn n w - F w
    have hg : DiffContOnCl ℂ g (ball z r) := (hn.diffContOnCl).sub hFcl
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
    obtain ⟨w, hw, hwzero⟩ := exists_zero_of_sphere_domination hr hg hFcl hz hg0 hdom
    refine ⟨w, hw, ?_⟩
    simpa only [g, sub_add_cancel] using hwzero

/-- **Closed-locus transfer on an open set.**  A zero of a not-identically-vanishing analytic limit
on a preconnected open set lies in every closed set containing the zeros of the approximants. -/
theorem mem_closed_of_tendstoLocallyUniformlyOn
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ} {Ω S : Set ℂ}
    (hΩ : IsOpen Ω) (hΩpre : IsPreconnected Ω)
    (hconv : TendstoLocallyUniformlyOn Fn F atTop Ω)
    (hF : AnalyticOnNhd ℂ F Ω)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hS : IsClosed S)
    (hzeroS : ∀ᶠ n in atTop, ∀ w, Fn n w = 0 → w ∈ S)
    {a z : ℂ} (haΩ : a ∈ Ω) (ha : F a ≠ 0) (hzΩ : z ∈ Ω) (hz : F z = 0) : z ∈ S := by
  rw [← hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 z, F w = 0 := by
    intro hev
    exact ha (hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩpre hzΩ hev haΩ)
  have hpunct : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 :=
    (hF z hzΩ).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnotEventuallyZero
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hΩ z hzΩ
  let r : ℝ := min (min (ε / 2) (δ / 2)) (ρ / 2)
  have hr : 0 < r := lt_min (lt_min (half_pos hε) (half_pos hδ)) (half_pos hρ)
  have hrε : r < ε :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (half_lt_self hε)
  have hrδ : r < δ :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (half_lt_self hδ)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ)
  have hball : closedBall z r ⊆ Ω := by
    refine le_trans (fun w hw => ?_) hρsub
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hrρ)
  have hsphere : ∀ w ∈ sphere z r, F w ≠ 0 := by
    intro w hw
    apply hδsub
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hrδ)
    · exact Set.mem_compl_singleton_iff.mpr (Metric.ne_of_mem_sphere hw hr.ne')
  have hlocal := eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn
    hconv hF hFn hr hball hz hsphere
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlocal
  obtain ⟨M, hM⟩ := eventually_atTop.1 hzeroS
  obtain ⟨w, hwball, hwzero⟩ := hN (max N M) (le_max_left _ _)
  refine ⟨w, hM (max N M) (le_max_right _ _) w hwzero, ?_⟩
  have hdist : dist z w ≤ r := by
    simpa [dist_comm] using Metric.mem_closedBall.mp hwball
  exact hdist.trans_lt hrε

/-! ## The corrected meromorphic wall -/

/-- **The corrected meromorphic reading of Suzuki's Corollary 1.6.**  Locally uniform convergence
of entire real-zero characteristic functions to the displayed quotient on a preconnected open set
that avoids the poles but retains the whole centered-Xi divisor. -/
def SuzukiXiMeromorphicCharacteristicLimitWall : Prop :=
  ∃ (Ω : Set ℂ) (W : ℕ → ℂ → ℂ),
    IsOpen Ω ∧ IsPreconnected Ω ∧
    {z : ℂ | XiC z = 0} ⊆ Ω ∧
    AnalyticOnNhd ℂ suzukiXiCharacteristicTarget Ω ∧
    TendstoLocallyUniformlyOn W suzukiXiCharacteristicTarget atTop Ω ∧
    (∀ᶠ n in atTop, Differentiable ℂ (W n)) ∧
    (∀ᶠ n in atTop, ∀ z : ℂ, W n z = 0 → z.im = 0) ∧
    ∃ a ∈ Ω, suzukiXiCharacteristicTarget a ≠ 0

/-- Under the corrected wall every centered Xi zero is real. -/
theorem im_eq_zero_of_suzukiXiMeromorphicCharacteristicLimitWall
    (h : SuzukiXiMeromorphicCharacteristicLimitWall) {z : ℂ} (hz : XiC z = 0) : z.im = 0 := by
  obtain ⟨Ω, W, hΩ, hΩpre, hzeros, hanalytic, hconv, hdiff, hreal, a, haΩ, hane⟩ := h
  have hzΩ : z ∈ Ω := hzeros hz
  have htarget : suzukiXiCharacteristicTarget z = 0 :=
    suzukiXiCharacteristicTarget_eq_zero_of_XiC_eq_zero hz
  have hmem := mem_closed_of_tendstoLocallyUniformlyOn hΩ hΩpre hconv hanalytic hdiff
    (isClosed_eq Complex.continuous_im continuous_const) hreal haΩ hane hzΩ htarget
  simpa using hmem

/-- **The corrected wall still implies the Riemann hypothesis.**  The repair of Suzuki's limit
topology does not weaken its arithmetic consequence. -/
theorem suzukiXiMeromorphicCharacteristicLimitWall_implies_riemannHypothesis
    (h : SuzukiXiMeromorphicCharacteristicLimitWall) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by
        rw [neg_mul, I_mul_I]
        ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have him : z.im = 0 := im_eq_zero_of_suzukiXiMeromorphicCharacteristicLimitWall h hXiC
  have hzIm : z.im = 1 / 2 - ρ.re := by
    simp [z]
  have hre : ρ.re = 1 / 2 := by linarith [him, hzIm]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) hre

/-! ## The pole of the displayed target -/

/-- **The pole from two real zeros.**  Two distinct positive real zeros of the centered completed
function produce a nonzero real point at which Suzuki's displayed target is not analytic. -/
theorem exists_pole_suzukiXiCharacteristicTarget_of_two_positive_real_XiC_zeros
    {a b : ℝ} (ha : 0 < a) (hab : a ≠ b)
    (hza : XiC (a : ℂ) = 0) (hzb : XiC (b : ℂ) = 0) (hb : 0 < b) :
    ∃ c : ℝ, 0 < c ∧ XiC (c : ℂ) ≠ 0 ∧ deriv XiC (c : ℂ) = 0 ∧
      ¬ AnalyticAt ℂ suzukiXiCharacteristicTarget (c : ℂ) := by
  obtain ⟨p, q, hp, hpq, hzp, hzq, hgap⟩ : ∃ p q : ℝ, 0 < p ∧ p < q ∧
      XiC (p : ℂ) = 0 ∧ XiC (q : ℂ) = 0 ∧ ∀ t ∈ Set.Ioo p q, XiC (t : ℂ) ≠ 0 := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact exists_positive_real_XiC_zero_gap_of_two_zeros ha hlt hza hzb
    · exact exists_positive_real_XiC_zero_gap_of_two_zeros hb hgt hzb hza
  obtain ⟨c, hc, hderiv⟩ := exists_deriv_XiC_eq_zero_between_real_zeros hpq hzp hzq
  have hcpos : 0 < c := lt_trans hp hc.1
  have hcne : (c : ℂ) ≠ 0 := by
    simpa using ne_of_gt hcpos
  have hcXi : XiC (c : ℂ) ≠ 0 := hgap c hc
  exact ⟨c, hcpos, hcXi, hderiv,
    not_analyticAt_suzukiXiCharacteristicTarget_of_deriv_eq_zero hcne hcXi hderiv⟩

/-- **Under the Riemann hypothesis the displayed target is not entire.**  This is the exact
unconditional strength of the pole obstruction: the entire-compact reading of Suzuki's limit is
incompatible with the very conclusion it is designed to produce. -/
theorem not_analyticOnNhd_suzukiXiCharacteristicTarget_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬ AnalyticOnNhd ℂ suzukiXiCharacteristicTarget Set.univ := by
  intro hanalytic
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ := exists_two_distinct_positive_real_XiC_zeros_of_rh hRH
  obtain ⟨c, _, _, _, hpole⟩ :=
    exists_pole_suzukiXiCharacteristicTarget_of_two_positive_real_XiC_zeros ha hab hza hzb hb
  exact hpole (hanalytic (c : ℂ) (Set.mem_univ _))

end

end RHTower
