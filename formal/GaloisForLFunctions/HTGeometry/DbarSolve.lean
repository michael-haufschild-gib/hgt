import GaloisForLFunctions.HTGeometry.CauchyPompeiu
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Solving the `∂̄` equation for a compactly supported source

For `g` of class `C¹` with compact support the Cauchy transform

`u(z) = (1/π) ∫_ℂ g(z − w)/w dA(w)`

solves `∂̄u = g`.  Differentiating under the integral sign is legitimate in this form because the
singularity does not move with `z` and the Cauchy kernel is locally integrable; the identity
`∂̄u = g` is then Cauchy–Pompeiu applied to `t ↦ g(z − t)` on a disc large enough to contain the
translated support, where the boundary circle mean vanishes.

* `HTGeometry.wirtingerAntiholL` : `∂̄` of a real-linear map, as a continuous linear functional.
* `HTGeometry.dbarSolution` : the Cauchy transform.
* `HTGeometry.exists_radius_of_hasCompactSupport` : a radius outside which `g` and `∂g` vanish.
-/

open Complex Real MeasureTheory Set

namespace HTGeometry

section AntiholFunctional

/-- The antiholomorphic Wirtinger part as a continuous linear functional on real-linear maps. -/
noncomputable def wirtingerAntiholL : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ((2 : ℝ)⁻¹ : ℝ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) +
    (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))

@[simp] theorem wirtingerAntiholL_apply (f' : ℂ →L[ℝ] ℂ) :
    wirtingerAntiholL f' = wirtingerAntihol f' := by
  rw [wirtingerAntiholL, wirtingerAntihol]
  simp [ContinuousLinearMap.apply, ContinuousLinearMap.mul]
  ring

end AntiholFunctional

section Support

variable {g : ℂ → ℂ}

/-- A radius outside which both `g` and its derivative vanish. -/
theorem exists_radius_of_hasCompactSupport (hcs : HasCompactSupport g) :
    ∃ S : ℝ, 0 < S ∧ (∀ w : ℂ, S ≤ ‖w‖ → g w = 0) ∧ ∀ w : ℂ, S ≤ ‖w‖ → fderiv ℝ g w = 0 := by
  obtain ⟨S₁, hS₁⟩ := hcs.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨S₂, hS₂⟩ := (hcs.fderiv ℝ).isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max (max S₁ S₂) 1 + 1, by positivity, ?_, ?_⟩
  · intro w hw
    refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
    have := hS₁ hc
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    have h1 : S₁ ≤ max (max S₁ S₂) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  · intro w hw
    refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
    have := hS₂ hc
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    have h2 : S₂ ≤ max (max S₁ S₂) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith

end Support

section CauchyTransform

/-- The Cauchy transform of `g`, the candidate solution of `∂̄u = g`. -/
noncomputable def dbarSolution (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((π : ℝ)⁻¹ : ℝ) • ∫ w : ℂ, g (z - w) / w


variable {g : ℂ → ℂ}

/-- **Differentiation of the Cauchy transform under the integral sign.**  The singularity does not
move with `z`, the derivative of the integrand is bounded by a constant multiple of the Cauchy
kernel restricted to a fixed ball, and that bound is integrable. -/
theorem hasFDerivAt_cauchyIntegral (hC : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z₀ : ℂ) :
    HasFDerivAt (fun z => ∫ w : ℂ, g (z - w) / w)
      (∫ w : ℂ, (w⁻¹ : ℂ) • fderiv ℝ g (z₀ - w)) z₀ := by
  obtain ⟨S, hSpos, hgS, hdS⟩ := exists_radius_of_hasCompactSupport hcs
  obtain ⟨M, hM⟩ := (hcs.fderiv ℝ).exists_bound_of_continuous (hC.continuous_fderiv one_ne_zero)
  have hd : Differentiable ℝ g := hC.differentiable one_ne_zero
  set T : ℝ := S + ‖z₀‖ + 1 with hT
  have hTpos : 0 < T := by positivity
  set bound : ℂ → ℝ := fun w => M * Set.indicator (Metric.ball (0 : ℂ) T) (fun w => ‖w‖⁻¹) w
    with hbound
  -- the derivative of `z ↦ g (z - w) / w`
  have hdiffpt : ∀ (w : ℂ), w ≠ 0 → ∀ z : ℂ,
      HasFDerivAt (fun z => g (z - w) / w) ((w⁻¹ : ℂ) • fderiv ℝ g (z - w)) z := by
    intro w hw z
    have h1 : HasFDerivAt (fun z : ℂ => g (z - w)) (fderiv ℝ g (z - w)) z := by
      have h2 := (hd (z - w)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const w)
      rw [ContinuousLinearMap.comp_id] at h2
      exact h2
    have heq : (fun z : ℂ => g (z - w) / w) = fun z : ℂ => (w⁻¹ : ℂ) • g (z - w) := by
      funext t
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [heq]
    exact h1.const_smul (w⁻¹ : ℂ)
  -- vanishing outside the ball
  have hvanish : ∀ (w : ℂ), w ∉ Metric.ball (0 : ℂ) T → ∀ z ∈ Metric.ball z₀ 1,
      fderiv ℝ g (z - w) = 0 := by
    intro w hw z hz
    refine hdS _ ?_
    simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
    simp only [Metric.mem_ball, Complex.dist_eq] at hz
    have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_sub_norm_le z z₀
      linarith [le_of_lt hz]
    have := norm_sub_norm_le z w
    have hn : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by
      rw [← norm_neg (z - w)]
      simpa [neg_sub] using norm_sub_norm_le w z
    linarith
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable (fun w : ℂ => g (z - w) / w) volume := by
    intro z
    exact ((hd.continuous.comp (continuous_const.sub continuous_id)).measurable.mul
      measurable_inv).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (fun w : ℂ => (w⁻¹ : ℂ) • fderiv ℝ g (z₀ - w)) volume := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_inv.smul
      (((hC.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).measurable)
  have hboundInt : Integrable bound volume := by
    rw [hbound]
    refine Integrable.const_mul ?_ M
    rw [MeasureTheory.integrable_indicator_iff measurableSet_ball]
    exact integrableOn_norm_inv_ball T
  have hFint : Integrable (fun w : ℂ => g (z₀ - w) / w) volume := by
    obtain ⟨M₀, hM₀⟩ := hcs.exists_bound_of_continuous hd.continuous
    refine MeasureTheory.Integrable.mono'
      (((MeasureTheory.integrable_indicator_iff (measurableSet_ball (x := (0 : ℂ)) (ε := T))).2
        (integrableOn_norm_inv_ball T)).const_mul (max M₀ 0)) (hmeasF z₀) ?_
    refine Filter.Eventually.of_forall (fun w => ?_)
    by_cases hw : w ∈ Metric.ball (0 : ℂ) T
    · rw [Set.indicator_of_mem hw, norm_div, div_eq_mul_inv]
      gcongr
      exact le_trans (hM₀ _) (le_max_left _ _)
    · have hz : g (z₀ - w) = 0 := by
        refine hgS _ ?_
        simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
        have hn : ‖w‖ - ‖z₀‖ ≤ ‖z₀ - w‖ := by
          rw [← norm_neg (z₀ - w)]
          simpa [neg_sub] using norm_sub_norm_le w z₀
        linarith
      rw [Set.indicator_of_notMem hw, hz]
      simp
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (bound := bound) (F' := fun z w => (w⁻¹ : ℂ) • fderiv ℝ g (z - w))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall (fun z => hmeasF z)) hFint hmeasF' ?_ hboundInt ?_
  · refine Filter.Eventually.of_forall (fun w => ?_)
    intro z hz
    show ‖(w⁻¹ : ℂ) • fderiv ℝ g (z - w)‖
      ≤ M * Set.indicator (Metric.ball (0 : ℂ) T) (fun w => ‖w‖⁻¹) w
    by_cases hw : w ∈ Metric.ball (0 : ℂ) T
    · rw [Set.indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
      gcongr
      exact hM _
    · rw [Set.indicator_of_notMem hw, hvanish w hw z hz, smul_zero, norm_zero]
      simp
  · filter_upwards [MeasureTheory.compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with w hw z _
    exact hdiffpt w (by simpa using hw) z


/-- The derivative kernel is integrable. -/
theorem integrable_fderivKernel (hC : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z : ℂ) :
    Integrable (fun w : ℂ => (w⁻¹ : ℂ) • fderiv ℝ g (z - w)) volume := by
  obtain ⟨S, hSpos, hgS, hdS⟩ := exists_radius_of_hasCompactSupport hcs
  obtain ⟨M, hM⟩ := (hcs.fderiv ℝ).exists_bound_of_continuous (hC.continuous_fderiv one_ne_zero)
  set T : ℝ := S + ‖z‖ + 1 with hT
  have hmeas : AEStronglyMeasurable (fun w : ℂ => (w⁻¹ : ℂ) • fderiv ℝ g (z - w)) volume := by
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_inv.smul
      (((hC.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).measurable)
  refine MeasureTheory.Integrable.mono'
    (((MeasureTheory.integrable_indicator_iff (measurableSet_ball (x := (0 : ℂ)) (ε := T))).2
      (integrableOn_norm_inv_ball T)).const_mul M) hmeas ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  by_cases hw : w ∈ Metric.ball (0 : ℂ) T
  · rw [Set.indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
    gcongr
    exact hM _
  · have hz : fderiv ℝ g (z - w) = 0 := by
      refine hdS _ ?_
      simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
      have hn : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by
        rw [← norm_neg (z - w)]
        simpa [neg_sub] using norm_sub_norm_le w z
      linarith
    rw [Set.indicator_of_notMem hw, hz, smul_zero, norm_zero]
    simp

/-- **Cauchy–Pompeiu for a compactly supported source.**  The `∂̄` Cauchy kernel of `g` integrates
to `π · g(z)`: the boundary circle mean vanishes once the disc contains the translated support. -/
theorem integral_dzbar_kernel (hC : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z : ℂ) :
    (∫ w : ℂ, dzbar g (z - w) / w) = (π : ℝ) • g z := by
  obtain ⟨S, hSpos, hgS, hdS⟩ := exists_radius_of_hasCompactSupport hcs
  have hd : Differentiable ℝ g := hC.differentiable one_ne_zero
  set R : ℝ := S + ‖z‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  set hfun : ℂ → ℂ := fun t => g (z - t) with hfundef
  have hCh : ContDiff ℝ 1 hfun := by
    have : ContDiff ℝ 1 (fun t : ℂ => z - t) := (contDiff_const.sub contDiff_id)
    exact hC.comp this
  -- outside the disc the source vanishes
  have houtside : ∀ w : ℂ, R ≤ ‖w‖ → dzbar g (z - w) = 0 := by
    intro w hw
    have hzw : S ≤ ‖z - w‖ := by
      have hn : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by
        rw [← norm_neg (z - w)]
        simpa [neg_sub] using norm_sub_norm_le w z
      linarith
    rw [dzbar, hdS _ hzw]
    simp [wirtingerAntihol]
  have hmean : circleMean hfun R = 0 := by
    rw [circleMean]
    have : ∀ θ : ℝ, hfun (circleMap 0 R θ) = 0 := by
      intro θ
      refine hgS _ ?_
      have hnorm : ‖circleMap 0 R θ‖ = R := by
        rw [norm_circleMap_zero, abs_of_pos hRpos]
      have hn : ‖circleMap 0 R θ‖ - ‖z‖ ≤ ‖z - circleMap 0 R θ‖ := by
        rw [← norm_neg (z - circleMap 0 R θ)]
        simpa [neg_sub] using norm_sub_norm_le (circleMap 0 R θ) z
      rw [hnorm] at hn
      linarith
    simp [this]
  have hCP := cauchyPompeiu_center (h := hfun) hCh hRpos
  rw [hmean] at hCP
  have hzero : hfun 0 = g z := by simp [hfundef]
  rw [hzero] at hCP
  have hdz : ∀ w : ℂ, dzbar hfun w = -dzbar g (z - w) := fun w => dzbar_comp_const_sub hd z w
  have hball : (∫ w in Metric.ball (0 : ℂ) R, dzbar hfun w / w)
      = -∫ w in Metric.ball (0 : ℂ) R, dzbar g (z - w) / w := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    rw [hdz w, neg_div]
  rw [hball] at hCP
  have hfull : (∫ w in Metric.ball (0 : ℂ) R, dzbar g (z - w) / w)
      = ∫ w : ℂ, dzbar g (z - w) / w := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => ?_)
    simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
    rw [houtside w hw, zero_div]
  rw [hfull] at hCP
  have h2 : (0 : ℂ) - (2 * π : ℝ) • g z = 2 * -(∫ w : ℂ, dzbar g (z - w) / w) := hCP
  have hπ : ((2 * π : ℝ) : ℂ) = 2 * ((π : ℝ) : ℂ) := by push_cast; ring
  simp only [Complex.real_smul] at h2 ⊢
  rw [hπ] at h2
  linear_combination h2 / 2

/-- **`∂̄u = g` for the Cauchy transform of a compactly supported `C¹` source.** -/
theorem dzbar_dbarSolution (hC : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z : ℂ) :
    dzbar (dbarSolution g) z = g z := by
  have hFD : HasFDerivAt (dbarSolution g)
      (((π : ℝ)⁻¹ : ℝ) • ∫ w : ℂ, (w⁻¹ : ℂ) • fderiv ℝ g (z - w)) z := by
    exact (hasFDerivAt_cauchyIntegral hC hcs z).const_smul (((π : ℝ)⁻¹ : ℝ))
  rw [dzbar_eq_of_hasFDerivAt hFD, ← wirtingerAntiholL_apply, map_smul,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_fderivKernel hC hcs z)]
  have hker : ∀ w : ℂ, wirtingerAntiholL ((w⁻¹ : ℂ) • fderiv ℝ g (z - w))
      = dzbar g (z - w) / w := by
    intro w
    rw [wirtingerAntiholL_apply, wirtingerAntihol_smul, dzbar, div_eq_mul_inv, mul_comm]
  simp only [hker]
  rw [integral_dzbar_kernel hC hcs z, smul_smul]
  rw [Complex.real_smul]
  have : ((π : ℝ)⁻¹ * π : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt Real.pi_pos)
  rw [this]
  simp

end CauchyTransform

section LocalSolvability

/-- **Local solvability of the `∂̄` equation in one variable.**  Cutting the source off by a smooth
bump reduces the problem to the compactly supported case, and the cut-off source agrees with the
original on the inner ball. -/
theorem exists_dbar_local (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ u : ℂ → ℂ, ∀ z ∈ Metric.closedBall z₀ r, dzbar u z = f z := by
  set chi : ContDiffBump z₀ := ⟨r, r + 1, hr, by linarith⟩ with hchi
  set g : ℂ → ℂ := fun z => (chi z : ℝ) • f z with hg
  have hchiC : ContDiff ℝ 1 (fun z => (chi z : ℝ)) := chi.contDiff (n := 1)
  have hgC : ContDiff ℝ 1 g := hchiC.smul hf
  have hgcs : HasCompactSupport g := chi.hasCompactSupport.smul_right
  refine ⟨dbarSolution g, fun z hz => ?_⟩
  rw [dzbar_dbarSolution hgC hgcs z, hg]
  simp only
  rw [chi.one_of_mem_closedBall hz, one_smul]

end LocalSolvability


end HTGeometry
