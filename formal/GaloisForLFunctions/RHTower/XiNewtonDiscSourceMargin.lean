import GaloisForLFunctions.RHTower.XiNewtonSchwarzPickCriticalLine
import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive

/-!
# Automatic holomorphy and the source margin of Xi Newton discs

The Newton map of Xi is locally bounded exactly where it is holomorphic: its only
singularities are critical points at which Xi does not vanish. Consequently a disc
self-mapping condition already supplies the holomorphy needed by Schwarz--Pick.

The denominator-free margin

`r² |xi'(z)|² - |(z-c) xi'(z) - xi(z)|²`

is positive precisely when a nonzero-derivative Newton step lands inside the disc.
Disc invariance is therefore equivalent to positivity of this explicit margin
at every nonzero value of Xi in the disc, with no separate regularity input.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower.XiNewtonCriticalLine

/-- The derivative of Xi is nonzero on a punctured neighborhood of every point. -/
theorem xi_deriv_eventually_ne_zero (p : ℂ) :
    ∀ᶠ z in 𝓝[≠] p, deriv xi z ≠ 0 := by
  refine ((xi_differentiable.analyticAt p).deriv.eventually_eq_zero_or_eventually_ne_zero).resolve_left ?_
  intro hzero
  have hglobal := xi_analyticOnNhd_univ.deriv.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ p) hzero
  have hd : deriv xi 1 = 0 := hglobal (mem_univ 1)
  have hpos := re_logDeriv_xi_pos_of_one_le_re (s := 1) (by simp)
  rw [logDeriv_apply, hd, zero_div, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- Local boundedness of the actual Xi Newton map. -/
def XiNewtonLocallyBounded (p : ℂ) : Prop :=
  ∃ M : ℝ, ∀ᶠ z in 𝓝 p, ‖newtonMap xi z‖ ≤ M

/-- Boundedness rules out precisely the nonroot critical points of Xi. -/
theorem xiNewtonLocallyBounded_iff (p : ℂ) :
    XiNewtonLocallyBounded p ↔ xi p = 0 ∨ deriv xi p ≠ 0 := by
  constructor
  · rintro ⟨M, hM⟩
    by_cases hd : deriv xi p = 0
    · left
      have hbound : ∀ᶠ z in 𝓝[≠] p,
          ‖xi z‖ ≤ (‖z‖ + M) * ‖deriv xi z‖ := by
        filter_upwards [xi_deriv_eventually_ne_zero p, nhdsWithin_le_nhds hM]
          with z hz hMz
        have hfactor : xi z = (z - newtonMap xi z) * deriv xi z := by
          simp only [newtonMap, sub_sub_cancel, div_mul_cancel₀ _ hz]
        rw [hfactor, norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((norm_sub_le z (newtonMap xi z)).trans (by linarith)) (norm_nonneg _)
      have hlimX : Tendsto (fun z => ‖xi z‖) (𝓝[≠] p) (𝓝 ‖xi p‖) :=
        ((xi_differentiable p).continuousAt.norm.tendsto).mono_left
        nhdsWithin_le_nhds
      have hlimA : Tendsto (fun z => ‖deriv xi z‖) (𝓝[≠] p) (𝓝 ‖deriv xi p‖) :=
        ((xi_differentiable.analyticAt p).deriv.continuousAt.norm.tendsto).mono_left
        nhdsWithin_le_nhds
      have hlimZ : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] p) (𝓝 ‖p‖) :=
        ((continuousAt_id (x := p)).norm.tendsto).mono_left nhdsWithin_le_nhds
      have hle := le_of_tendsto_of_tendsto hlimX
        ((hlimZ.add tendsto_const_nhds).mul hlimA) hbound
      rw [hd, norm_zero, mul_zero] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    · exact Or.inr hd
  · intro h
    have hcont : ContinuousAt (newtonMap xi) p := by
      rcases h with hzero | hderiv
      · obtain ⟨r, hr, hdiff, -⟩ := exists_ball_newton_invariant_of_zero
          xi_differentiable hzero (xi_not_eventually_zero p)
        exact (hdiff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt
      · exact continuousAt_id.sub ((xi_differentiable p).continuousAt.div
          (xi_differentiable.analyticAt p).deriv.continuousAt hderiv)
    refine ⟨‖newtonMap xi p‖ + 1, ?_⟩
    exact (hcont.norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le

/-- Exact holomorphy locus of the actual Xi Newton map, including multiple roots. -/
theorem analyticAt_xi_newton_iff (p : ℂ) :
    AnalyticAt ℂ (newtonMap xi) p ↔ xi p = 0 ∨ deriv xi p ≠ 0 := by
  constructor
  · intro h
    apply (xiNewtonLocallyBounded_iff p).mp
    exact ⟨‖newtonMap xi p‖ + 1,
      (h.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ hz => hz.le⟩
  · rintro (hzero | hderiv)
    · obtain ⟨r, hr, hdiff, -⟩ := exists_ball_newton_invariant_of_zero
        xi_differentiable hzero (xi_not_eventually_zero p)
      exact hdiff.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    · exact analyticAt_id.sub ((xi_differentiable.analyticAt p).div
        (xi_differentiable.analyticAt p).deriv hderiv)

/-- Boundedness and holomorphy are equivalent for the actual Xi Newton map. -/
theorem xiNewtonLocallyBounded_iff_analyticAt (p : ℂ) :
    XiNewtonLocallyBounded p ↔ AnalyticAt ℂ (newtonMap xi) p := by
  rw [xiNewtonLocallyBounded_iff, analyticAt_xi_newton_iff]

/-- Mapping into a closed disc also supplies holomorphy on its open interior. -/
theorem xi_newton_mapsTo_closedBall_iff_holomorphic_map (c : ℂ) (r : ℝ) :
    MapsTo (newtonMap xi) (ball c r) (closedBall c r) ↔
      DifferentiableOn ℂ (newtonMap xi) (ball c r) ∧
        MapsTo (newtonMap xi) (ball c r) (closedBall c r) := by
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  intro p hp
  apply AnalyticAt.differentiableWithinAt
  apply (xiNewtonLocallyBounded_iff_analyticAt p).mp
  refine ⟨r + ‖c‖, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hp] with z hz
  have hdist := h hz
  rw [mem_closedBall, dist_eq_norm] at hdist
  have htri : ‖newtonMap xi z‖ ≤ ‖newtonMap xi z - c‖ + ‖c‖ := by
    simpa [dist_eq_norm] using dist_triangle (newtonMap xi z) c 0
  linarith

/-- Every self-mapped Xi Newton disc automatically has a holomorphic Newton map. -/
theorem xi_newton_mapsTo_ball_iff_holomorphic_selfmap (c : ℂ) (r : ℝ) :
    MapsTo (newtonMap xi) (ball c r) (ball c r) ↔
      DifferentiableOn ℂ (newtonMap xi) (ball c r) ∧
        MapsTo (newtonMap xi) (ball c r) (ball c r) := by
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  exact ((xi_newton_mapsTo_closedBall_iff_holomorphic_map c r).mp
    (h.mono_right ball_subset_closedBall)).1

/-- The Newton disc margin expressed using only Xi and its first derivative. -/
def xiNewtonDiscMargin (c : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  r ^ 2 * normSq (deriv xi z) - normSq ((z - c) * deriv xi z - xi z)

/-- The source margin has no quotient singularities. -/
theorem continuous_xiNewtonDiscMargin (c : ℂ) (r : ℝ) :
    Continuous (xiNewtonDiscMargin c r) := by
  have hA : Continuous (deriv xi) :=
    continuous_iff_continuousAt.mpr fun z => (xi_differentiable.analyticAt z).deriv.continuousAt
  have hX : Continuous xi := xi_differentiable.continuous
  unfold xiNewtonDiscMargin
  fun_prop

private theorem xiNewtonDiscMargin_factor {c z : ℂ} {r : ℝ} (hd : deriv xi z ≠ 0) :
    xiNewtonDiscMargin c r z =
      (r ^ 2 - normSq (newtonMap xi z - c)) * normSq (deriv xi z) := by
  have hfactor : (z - c) * deriv xi z - xi z =
      (newtonMap xi z - c) * deriv xi z := by
    simp only [newtonMap]
    field_simp
    ring
  rw [xiNewtonDiscMargin, hfactor, Complex.normSq_mul]
  ring

/-- Nonnegative interior source margin is exactly mapping into the closed disc. -/
theorem xi_newton_mapsTo_closedBall_iff_source_margin (c : ℂ) (r : ℝ) :
    MapsTo (newtonMap xi) (ball c r) (closedBall c r) ↔
      ∀ z ∈ ball c r, 0 ≤ xiNewtonDiscMargin c r z := by
  constructor
  · intro h z hz
    by_cases hd : deriv xi z = 0
    · have han := (((xi_newton_mapsTo_closedBall_iff_holomorphic_map c r).mp h).1).analyticAt
        (isOpen_ball.mem_nhds hz)
      have hzero := ((analyticAt_xi_newton_iff z).mp han).resolve_right (not_not.mpr hd)
      simp [xiNewtonDiscMargin, hd, hzero]
    · rw [xiNewtonDiscMargin_factor hd]
      apply mul_nonneg _ (normSq_nonneg _)
      have hmem := h hz
      rw [mem_closedBall, dist_eq_norm] at hmem
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (newtonMap xi z - c)]
  · intro h z hz
    have hmargin := h z hz
    by_cases hd : deriv xi z = 0
    · have hzero : xi z = 0 := by
        simp only [xiNewtonDiscMargin, hd, normSq_zero, mul_zero, zero_sub,
          normSq_neg] at hmargin
        exact normSq_eq_zero.mp (le_antisymm (by linarith) (normSq_nonneg _))
      rw [newtonMap_eq_self_of_eq_zero hzero]
      exact ball_subset_closedBall hz
    · rw [xiNewtonDiscMargin_factor hd] at hmargin
      have hsq := (mul_nonneg_iff_of_pos_right (Complex.normSq_pos.mpr hd)).mp hmargin
      rw [Complex.normSq_eq_norm_sq] at hsq
      have hr : 0 < r := (mem_ball.mp hz).trans_le' dist_nonneg
      rw [mem_closedBall, dist_eq_norm]
      nlinarith [norm_nonneg (newtonMap xi z - c)]

/-- Disc invariance is exactly positivity of the source margin away from Xi zeros. -/
theorem xi_newton_mapsTo_ball_iff_source_margin (c : ℂ) (r : ℝ) :
    MapsTo (newtonMap xi) (ball c r) (ball c r) ↔
      ∀ z ∈ ball c r, xi z = 0 ∨ 0 < xiNewtonDiscMargin c r z := by
  constructor
  · intro h z hz
    by_cases hzero : xi z = 0
    · exact Or.inl hzero
    · right
      have han := (((xi_newton_mapsTo_ball_iff_holomorphic_selfmap c r).mp h).1).analyticAt
        (isOpen_ball.mem_nhds hz)
      have hd := ((analyticAt_xi_newton_iff z).mp han).resolve_left hzero
      rw [xiNewtonDiscMargin_factor hd]
      apply mul_pos _ (Complex.normSq_pos.mpr hd)
      have hmem := h hz
      rw [mem_ball, dist_eq_norm] at hmem
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (newtonMap xi z - c)]
  · intro h z hz
    rcases h z hz with hzero | hmargin
    · rwa [newtonMap_eq_self_of_eq_zero hzero]
    · have hd : deriv xi z ≠ 0 := by
        intro hzero
        simp only [xiNewtonDiscMargin, hzero, normSq_zero, mul_zero,
          zero_sub, normSq_neg] at hmargin
        linarith [normSq_nonneg (xi z)]
      rw [xiNewtonDiscMargin_factor hd] at hmargin
      have hsq := (mul_pos_iff_of_pos_right (Complex.normSq_pos.mpr hd)).mp hmargin
      rw [Complex.normSq_eq_norm_sq] at hsq
      have hr : 0 < r := (mem_ball.mp hz).trans_le' dist_nonneg
      rw [mem_ball, dist_eq_norm]
      nlinarith [norm_nonneg (newtonMap xi z - c)]

/-- The Newton receiver needs only disc self-mapping; holomorphy follows. -/
theorem riemannHypothesis_iff_xi_newton_disc_selfmaps :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 →
      ∃ c : ℂ, c.re = 1 / 2 ∧ ∃ r > 0, ρ ∈ ball c r ∧
        MapsTo (newtonMap xi) (ball c r) (ball c r) := by
  rw [riemannHypothesis_iff_newton_invariant_critical_discs]
  simp_rw [← xi_newton_mapsTo_ball_iff_holomorphic_selfmap]

/-- An exact source-margin form of the line-centered Newton-disc receiver. -/
theorem riemannHypothesis_iff_xi_newton_source_margin :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 →
      ∃ c : ℂ, c.re = 1 / 2 ∧ ∃ r > 0, ρ ∈ ball c r ∧
        ∀ z ∈ ball c r, xi z = 0 ∨ 0 < xiNewtonDiscMargin c r z := by
  rw [riemannHypothesis_iff_xi_newton_disc_selfmaps]
  simp_rw [xi_newton_mapsTo_ball_iff_source_margin]

/-- Weak interior margin suffices: a contained Xi zero rules out a boundary-valued constant map. -/
theorem riemannHypothesis_iff_xi_newton_nonnegative_margin :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 →
      ∃ c : ℂ, c.re = 1 / 2 ∧ ∃ r > 0, ρ ∈ ball c r ∧
        ∀ z ∈ ball c r, 0 ≤ xiNewtonDiscMargin c r z := by
  rw [riemannHypothesis_iff_xi_newton_disc_selfmaps]
  constructor
  · intro h ρ hzero
    obtain ⟨c, hc, r, hr, hρ, hmap⟩ := h ρ hzero
    exact ⟨c, hc, r, hr, hρ,
      (xi_newton_mapsTo_closedBall_iff_source_margin c r).mp
        (hmap.mono_right ball_subset_closedBall)⟩
  · intro h ρ hzero
    obtain ⟨c, hc, r, hr, hρ, hmargin⟩ := h ρ hzero
    have hclosed := (xi_newton_mapsTo_closedBall_iff_source_margin c r).mpr hmargin
    have hdiff := ((xi_newton_mapsTo_closedBall_iff_holomorphic_map c r).mp hclosed).1
    refine ⟨c, hc, r, hr, hρ, ?_⟩
    intro z hz
    have hle : ‖newtonMap xi z - c‖ ≤ r := by
      simpa only [mem_closedBall, dist_eq_norm] using hclosed hz
    rw [mem_ball, dist_eq_norm]
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hmax : IsMaxOn (norm ∘ (fun w => newtonMap xi w - c)) (ball c r) z := by
      intro w hw
      change ‖newtonMap xi w - c‖ ≤ ‖newtonMap xi z - c‖
      rw [heq]
      simpa only [mem_closedBall, dist_eq_norm] using hclosed hw
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (convex_ball c r).isPreconnected isOpen_ball (hdiff.sub_const c) hz hmax
    have hval : newtonMap xi ρ - c = newtonMap xi z - c := hconst hρ
    rw [newtonMap_eq_self_of_eq_zero hzero] at hval
    have hnorm : ‖ρ - c‖ = r := (congrArg norm hval).trans heq
    have hlt : ‖ρ - c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hρ
    exact (ne_of_lt hlt) hnorm

end RHTower.XiNewtonCriticalLine
