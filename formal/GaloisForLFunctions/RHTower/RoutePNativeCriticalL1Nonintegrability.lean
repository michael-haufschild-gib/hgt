import GaloisForLFunctions.RHTower.RoutePNativeCriticalSquareEnergy
import GaloisForLFunctions.HTGeometry.BochnerLaplaceHolomorphy

/-!
# The native critical profile has infinite absolute mass

Absolute admission would bound the source Laplace transform up to the
imaginary axis. Analytic rigidity then contradicts its nonzero residue at
an unconditional critical-line zero. This L1 obstruction is independent
of the earlier L2 obstruction; neither is a positive-damping energy bound.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

private theorem source_bochner_eq_causal :
    bochnerLaplaceRay (fun t => (routePSourceRay t : ℂ)) =
      causalTransform (fun t => (routePSourceRay t : ℂ)) := by
  funext z
  unfold bochnerLaplaceRay causalTransform
  congr 1
  funext t
  simp only [expRay, smul_eq_mul, neg_mul]

private theorem source_laplace_analytic_of_integrable
    (hg : IntegrableOn routePSourceRay (Ioi 0)) :
    AnalyticOnNhd ℂ (causalTransform (fun t => (routePSourceRay t : ℂ)))
      {z : ℂ | 0 < z.re} := by
  have hm : AEStronglyMeasurable (fun t => (routePSourceRay t : ℂ)) volume :=
    (Complex.continuous_ofReal.comp
      GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative).aestronglyMeasurable
  have hi : IntegrableOn (fun t => expRay (0 : ℂ) t • (routePSourceRay t : ℂ))
      (Ioi 0) := by simpa [expRay, IntegrableOn] using hg.ofReal (𝕜 := ℂ)
  have hd : DifferentiableOn ℂ (causalTransform (fun t => (routePSourceRay t : ℂ)))
      {z : ℂ | 0 < z.re} := by
    intro z hz
    have h := (bochnerLaplaceRay_differentiableAt hm hi z hz).differentiableWithinAt
      (s := {z : ℂ | 0 < z.re})
    rwa [source_bochner_eq_causal] at h
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

private theorem source_boundary_residue_zero_of_integrable
    (hg : IntegrableOn routePSourceRay (Ioi 0)) (z0 : ℂ) (hz0 : z0.re = 0) :
    Tendsto (fun σ : ℝ => (σ : ℂ) *
      causalTransform (fun t => (routePSourceRay t : ℂ)) ((σ : ℂ) + z0))
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := ∫ t in Ioi 0, ‖(routePSourceRay t : ℂ)‖
  have hi : IntegrableOn (fun t => expRay (0 : ℂ) t • (routePSourceRay t : ℂ))
      (Ioi 0) := by simpa [expRay, IntegrableOn] using hg.ofReal (𝕜 := ℂ)
  have hσ : Tendsto (fun σ : ℝ => σ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun σ : ℝ => σ * C) (𝓝[>] 0) (𝓝 0) by
      simpa using hσ.mul_const C)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with σ hσpos
    have hbound := bochnerLaplaceRay_norm_le hi ((σ : ℂ) + z0)
      (by simpa [hz0] using hσpos.le)
    have hb : ‖causalTransform (fun t => (routePSourceRay t : ℂ))
        ((σ : ℂ) + z0)‖ ≤ C := by
      simpa only [source_bochner_eq_causal, expRay, Complex.ofReal_zero,
        zero_mul, neg_zero, Complex.exp_zero, one_smul, C] using hbound
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσpos]
    exact mul_le_mul_of_nonneg_left hb hσpos.le

/-- The literal Route-P source has no finite undamped absolute mass. -/
theorem not_integrableOn_routePSourceRay :
    ¬ IntegrableOn routePSourceRay (Ioi 0) := by
  intro hg
  have hL := source_laplace_analytic_of_integrable hg
  obtain ⟨T0, hT0, hT⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, hτ, hzero⟩ := hT T0 le_rfl
  have hτ0 : 0 < τ := lt_of_lt_of_le hT0 hτ.1
  have him : 0 < (linePt τ).im := by simpa only [linePt_im] using hτ0
  obtain ⟨m, hm, hres⟩ := routePSourceLaplaceContinuation_residue_of_zero hzero him
  let z0 : ℂ := linePt τ - 1 / 2
  have hz0 : z0.re = 0 := by simp [z0, linePt]
  have hσ : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun σ : ℝ => (σ : ℂ) + z0) (𝓝[>] 0) (𝓝[≠] z0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hσ.add_const z0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσpos
    change (σ : ℂ) + z0 ≠ z0
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re, hz0, add_zero] at hre
    exact (ne_of_gt hσpos) hre
  have hpole : Tendsto (fun σ : ℝ => (σ : ℂ) *
      routePSourceLaplaceContinuation ((σ : ℂ) + z0)) (𝓝[>] 0)
      (𝓝 (-(m : ℂ) / (linePt τ * (linePt τ + 1 / 2)))) := by
    simpa only [Function.comp_def, z0, add_sub_cancel_right] using hres.comp hp
  have hvanish : Tendsto (fun σ : ℝ => (σ : ℂ) *
      routePSourceLaplaceContinuation ((σ : ℂ) + z0)) (𝓝[>] 0) (𝓝 0) := by
    apply (source_boundary_residue_zero_of_integrable hg z0 hz0).congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσpos
    rw [routePSource_transform_eq_continuation_of_analytic hL (by simpa [hz0] using hσpos)]
  have hne : -(m : ℂ) / (linePt τ * (linePt τ + 1 / 2)) ≠ 0 := by
    apply div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
    apply mul_ne_zero
    · intro heq
      have h := congrArg Complex.im heq
      simp only [linePt_im, Complex.zero_im] at h
      linarith
    · intro heq
      have h := congrArg Complex.im heq
      simp [linePt_im] at h
      linarith
  exact hne (tendsto_nhds_unique hpole hvanish)

/-- The complete native Möbius head has infinite critical absolute mass. -/
theorem not_integrableOn_routePNativeCriticalProfile :
    ¬ IntegrableOn routePNativeCriticalProfile (Ioi 0) := by
  intro hi
  apply not_integrableOn_routePSourceRay
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t / 2)) (Ioi 0) := by
    simpa only [show ∀ t : ℝ, (-1 / 2 : ℝ) * t = -t / 2 by intro t; ring] using
      integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0
  apply ((hi.norm.const_mul 2).add (he.const_mul (20 / 3 : ℝ))).mono'
    GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hd := criticalAbel_routeP_difference_le ht.le
  rw [← mobiusDivisorFullHead_eq_criticalContinuousAbel] at hd
  have hd' : 0 < 2 * routePNativeCriticalProfile t - routePSourceRay t ∧
      2 * routePNativeCriticalProfile t - routePSourceRay t ≤
        20 / 3 * Real.exp (-t / 2) := by
    simpa only [routePNativeCriticalProfile, mul_assoc, neg_div] using hd
  simp only [Real.norm_eq_abs]
  have htriangle := abs_add_le (2 * routePNativeCriticalProfile t)
    (-(2 * routePNativeCriticalProfile t - routePSourceRay t))
  rw [show 2 * routePNativeCriticalProfile t +
      -(2 * routePNativeCriticalProfile t - routePSourceRay t) = routePSourceRay t by ring,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_neg, abs_of_pos hd'.1] at htriangle
  apply htriangle.trans
  dsimp only [Pi.add_apply]
  linarith only [hd'.2]

end RHTower
