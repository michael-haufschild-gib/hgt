import GaloisForLFunctions.RHTower.PerturbationZero

/-!
# Nonvanishing survives uniform convergence inside a disk

The local Hurwitz argument uses the existing sphere-domination lemma. Entire
continuation is not required for the valuation residue functions.
-/

open Complex Metric Set Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem disk_zero_free_of_uniform_limit {α : Type*} {L : Filter α} [L.NeBot]
    {F : ℂ → ℂ} {Fn : α → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (ball 0 R)) (hF0 : F 0 ≠ 0)
    (hFn : ∀ᶠ n in L, DifferentiableOn ℂ (Fn n) (ball 0 R))
    (hne : ∀ᶠ n in L, ∀ z ∈ ball 0 R, Fn n z ≠ 0)
    (hconv : ∀ r : ℝ, 0 ≤ r → r < R →
      TendstoUniformlyOn Fn F L (closedBall 0 r)) :
    ∀ z ∈ ball 0 R, F z ≠ 0 := by
  intro z hz hzero
  have ha := hF.analyticOnNhd isOpen_ball
  have hnot : ¬ ∀ᶠ w in 𝓝 z, F w = 0 := by
    intro he
    exact hF0 (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) R).isPreconnected hz he (mem_ball_self hR))
  have hpunct : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 :=
    (ha z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
  obtain ⟨delta, hdelta, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  have hzR : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  obtain ⟨S, hzS, hSR⟩ := exists_between hzR
  have hS : 0 ≤ S := (norm_nonneg z).trans hzS.le
  let r := min (delta / 2) ((S - ‖z‖) / 2)
  have hr : 0 < r := lt_min (half_pos hdelta) (half_pos (sub_pos.mpr hzS))
  have hrdelta : r < delta := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hdelta)
  have hrS : r + ‖z‖ < S := by
    have hh := min_le_right (delta / 2) ((S - ‖z‖) / 2)
    dsimp only [r]
    linarith
  have hclosedSmall : closedBall z r ⊆ closedBall (0 : ℂ) S := by
    intro w hw
    have hwz : dist w z ≤ r := mem_closedBall.mp hw
    have ht : ‖w‖ ≤ dist w z + ‖z‖ := by
      simpa only [dist_zero_right] using dist_triangle w z (0 : ℂ)
    have hws : ‖w‖ ≤ S := by linarith
    simpa only [mem_closedBall, dist_zero_right] using hws
  have hclosed : closedBall z r ⊆ ball (0 : ℂ) R := by
    intro w hw
    have hwS : ‖w‖ ≤ S := by
      simpa only [mem_closedBall, dist_zero_right] using hclosedSmall hw
    simpa only [mem_ball, dist_zero_right] using hwS.trans_lt hSR
  have hsphere : ∀ w ∈ sphere z r, F w ≠ 0 := by
    intro w hw
    apply hsub
    refine ⟨?_, ?_⟩
    · exact mem_ball.mpr ((mem_sphere.mp hw).trans_lt hrdelta)
    · exact mem_compl_singleton_iff.mpr (Metric.ne_of_mem_sphere hw hr.ne')
  have hsphereClosed : sphere z r ⊆ closedBall z r := by
    intro w hw
    exact mem_closedBall.mpr (mem_sphere.mp hw).le
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (hF.continuousOn.mono (fun w hw => hclosed (hsphereClosed hw))).norm
  have hminPos : 0 < ‖F w₀‖ := norm_pos_iff.mpr (hsphere w₀ hw₀)
  have hclose : ∀ᶠ n in L, ∀ w ∈ closedBall (0 : ℂ) S,
      dist (F w) (Fn n w) < ‖F w₀‖ / 3 :=
    (Metric.tendstoUniformlyOn_iff.mp (hconv S hS hSR)) (‖F w₀‖ / 3)
      (div_pos hminPos (by norm_num))
  obtain ⟨n, hdn, hnn, hcn⟩ := (hFn.and (hne.and hclose)).exists
  let g : ℂ → ℂ := fun w => Fn n w - F w
  have hgd : DifferentiableOn ℂ g (ball 0 R) := hdn.sub hF
  have hg : DiffContOnCl ℂ g (ball z r) := by
    constructor
    · exact hgd.mono (fun w hw => hclosed (ball_subset_closedBall hw))
    · rw [closure_ball z hr.ne']
      exact hgd.continuousOn.mono hclosed
  have hf : DiffContOnCl ℂ F (ball z r) := by
    constructor
    · exact hF.mono (fun w hw => hclosed (ball_subset_closedBall hw))
    · rw [closure_ball z hr.ne']
      exact hF.continuousOn.mono hclosed
  have hg0 : g z ≠ 0 := by simpa only [g, hzero, sub_zero] using hnn z hz
  have hdom : ∀ w ∈ sphere z r, 3 * ‖g w‖ ≤ ‖F w‖ := by
    intro w hw
    have hc := hcn w (hclosedSmall (hsphereClosed hw))
    have hm : ‖F w₀‖ ≤ ‖F w‖ := hmin hw
    have he : ‖g w‖ = dist (F w) (Fn n w) := by
      simp only [g, dist_eq_norm, norm_sub_rev]
    rw [he]
    linarith
  obtain ⟨w, hw, hw0⟩ := RHTower.exists_zero_of_sphere_domination hr hg hf hzero hg0 hdom
  exact hnn w (hclosed hw) (by simpa only [g, sub_add_cancel] using hw0)

end RHTower.WeilSingularArithmetic
