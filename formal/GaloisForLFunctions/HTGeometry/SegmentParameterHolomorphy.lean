import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Holomorphy of an integral along the unit parameter segment

If `G` is holomorphic on an open set `U` which is star-shaped about the origin, and `w` is a bounded
continuous weight on `[0,1]`, then

`Φ(z) = ∫₀¹ w(s) G(zs) ds`

is holomorphic on `U`.  This is the parameterised form of a contour integral along the segment from
the origin, and the point is that no branch or path dependence survives: the parameter `s` is real
and the integrand is holomorphic in `z` for each `s`.

The proof is differentiation under the integral sign.  The dominating bound comes from the fact that
the cone `[0,1] · closedBall z₀ ε` is a compact subset of `U`, so the derivative of `G` — continuous
because a complex differentiable function on an open set is analytic there — is bounded on it.
-/

open MeasureTheory Set Filter Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **Differentiation under the integral along the unit parameter segment.**  On a star-shaped open
set the integral of a holomorphic integrand against a bounded continuous weight is holomorphic, with
the expected derivative. -/
theorem hasDerivAt_integral_unitSegment {U : Set ℂ} (hU : IsOpen U)
    (hstar : ∀ z ∈ U, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → z * (s : ℂ) ∈ U)
    {G : ℂ → X} (hG : DifferentiableOn ℂ G U)
    {w : ℝ → ℂ} {M : ℝ} (hwc : ContinuousOn w (Icc (0 : ℝ) 1))
    (hwb : ∀ s ∈ Icc (0 : ℝ) 1, ‖w s‖ ≤ M)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    HasDerivAt (fun z => ∫ s in (0 : ℝ)..1, w s • G (z * (s : ℂ)))
      (∫ s in (0 : ℝ)..1, (w s * (s : ℂ)) • deriv G (z₀ * (s : ℂ))) z₀ := by
  classical
  obtain ⟨ε, hε, hball⟩ : ∃ ε : ℝ, 0 < ε ∧ closedBall z₀ ε ⊆ U := by
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
    exact ⟨r / 2, by linarith, fun y hy => hrU (closedBall_subset_ball (by linarith) hy)⟩
  -- the compact cone swept by the segments
  set K : Set ℂ := (fun p : ℝ × ℂ => p.2 * (p.1 : ℂ)) '' (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ ε)
    with hKdef
  have hKcomp : IsCompact K := by
    rw [hKdef]
    exact (isCompact_Icc.prod (isCompact_closedBall z₀ ε)).image (by fun_prop)
  have hKU : K ⊆ U := by
    rw [hKdef]
    rintro _ ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
    exact hstar z (hball hz) s hs
  have hKne : K.Nonempty := by
    refine ⟨z₀, ?_⟩
    rw [hKdef]
    exact ⟨(1, z₀), ⟨⟨zero_le_one, le_rfl⟩, mem_closedBall_self hε.le⟩, by simp⟩
  -- the derivative of `G` is continuous on `U`
  have hGa : AnalyticOnNhd ℂ G U := hG.analyticOnNhd hU
  have hdercont : ContinuousOn (deriv G) U := hGa.deriv.continuousOn
  obtain ⟨u₀, hu₀K, hu₀max⟩ :=
    hKcomp.exists_isMaxOn hKne ((hdercont.mono hKU).norm)
  set N : ℝ := ‖deriv G u₀‖ with hNdef
  have hN0 : 0 ≤ N := norm_nonneg _
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hwb 0 ⟨le_rfl, zero_le_one⟩)
  -- membership of the swept points
  have hmemK : ∀ z ∈ closedBall z₀ ε, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → z * (s : ℂ) ∈ K := by
    intro z hz s hs
    rw [hKdef]
    exact ⟨(s, z), ⟨hs, hz⟩, rfl⟩
  have hmemU : ∀ z ∈ closedBall z₀ ε, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → z * (s : ℂ) ∈ U :=
    fun z hz s hs => hKU (hmemK z hz s hs)
  -- the integrand and its derivative
  set F : ℂ → ℝ → X := fun z s => w s • G (z * (s : ℂ)) with hFdef
  set F' : ℂ → ℝ → X := fun z s => (w s * (s : ℂ)) • deriv G (z * (s : ℂ)) with hF'def
  have hcontF : ∀ z ∈ closedBall z₀ ε, ContinuousOn (F z) (Icc (0 : ℝ) 1) := by
    intro z hz
    refine ContinuousOn.smul hwc ?_
    refine ContinuousOn.comp (hG.continuousOn) ?_ (fun s hs => hmemU z hz s hs)
    fun_prop
  have hcontF' : ∀ z ∈ closedBall z₀ ε, ContinuousOn (F' z) (Icc (0 : ℝ) 1) := by
    intro z hz
    refine ContinuousOn.smul (hwc.mul (by fun_prop)) ?_
    refine ContinuousOn.comp hdercont ?_ (fun s hs => hmemU z hz s hs)
    fun_prop
  have hmeas : ∀ z ∈ closedBall z₀ ε,
      AEStronglyMeasurable (F z) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro z hz
    refine ((hcontF z hz).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hintF : ∀ z ∈ closedBall z₀ ε, Integrable (F z) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    fun z hz => ((hcontF z hz).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hmeas' : AEStronglyMeasurable (F' z₀) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((hcontF' z₀ (mem_closedBall_self hε.le)).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  -- domination
  have hbound : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ∀ z ∈ ball z₀ ε, ‖F' z s‖ ≤ M * N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs z hz
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
    have hzc : z ∈ closedBall z₀ ε := ball_subset_closedBall hz
    have hws : ‖w s * (s : ℂ)‖ ≤ M := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsIcc.1]
      calc ‖w s‖ * s ≤ M * 1 := by
            refine mul_le_mul (hwb s hsIcc) hsIcc.2 hsIcc.1 hM0
        _ = M := mul_one M
    have hder : ‖deriv G (z * (s : ℂ))‖ ≤ N := hu₀max (hmemK z hzc s hsIcc)
    calc ‖F' z s‖ = ‖w s * (s : ℂ)‖ * ‖deriv G (z * (s : ℂ))‖ := by
          rw [hF'def, norm_smul]
      _ ≤ M * N := mul_le_mul hws hder (norm_nonneg _) hM0
  have hboundint : Integrable (fun _ : ℝ => M * N) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
      constructor
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    exact integrable_const _
  -- the derivative in the parameter
  have hderiv : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ∀ z ∈ ball z₀ ε, HasDerivAt (fun z => F z s) (F' z s) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs z hz
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
    have hzc : z ∈ closedBall z₀ ε := ball_subset_closedBall hz
    have hlin : HasDerivAt (fun z : ℂ => z * (s : ℂ)) ((s : ℂ)) z := by
      simpa using (hasDerivAt_id z).mul_const ((s : ℂ))
    have hGd : HasDerivAt G (deriv G (z * (s : ℂ))) (z * (s : ℂ)) :=
      (hG.differentiableAt (hU.mem_nhds (hmemU z hzc s hsIcc))).hasDerivAt
    have hcomp : HasDerivAt (fun z : ℂ => G (z * (s : ℂ)))
        ((s : ℂ) • deriv G (z * (s : ℂ))) z := HasDerivAt.scomp z hGd hlin
    show HasDerivAt (fun z : ℂ => w s • G (z * (s : ℂ)))
      ((w s * (s : ℂ)) • deriv G (z * (s : ℂ))) z
    rw [← smul_smul]
    exact hcomp.const_smul (w s)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) (bound := fun _ : ℝ => M * N) (F := F) (F' := F')
    (x₀ := z₀) (s := ball z₀ ε) (ball_mem_nhds z₀ hε)
    (by filter_upwards [ball_mem_nhds z₀ hε] with z hz
          using hmeas z (ball_subset_closedBall hz))
    (hintF z₀ (mem_closedBall_self hε.le)) hmeas' hbound hboundint hderiv
  have hrw : (fun z : ℂ => ∫ s in (0 : ℝ)..1, w s • G (z * (s : ℂ)))
      = fun z : ℂ => ∫ s : ℝ, F z s ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    funext z
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hrw' : (∫ s in (0 : ℝ)..1, (w s * (s : ℂ)) • deriv G (z₀ * (s : ℂ)))
      = ∫ s : ℝ, F' z₀ s ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hrw, hrw']
  exact hmain.2

/-- **Holomorphy of a segment-parameter integral.** -/
theorem differentiableAt_integral_unitSegment {U : Set ℂ} (hU : IsOpen U)
    (hstar : ∀ z ∈ U, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → z * (s : ℂ) ∈ U)
    {G : ℂ → X} (hG : DifferentiableOn ℂ G U)
    {w : ℝ → ℂ} {M : ℝ} (hwc : ContinuousOn w (Icc (0 : ℝ) 1))
    (hwb : ∀ s ∈ Icc (0 : ℝ) 1, ‖w s‖ ≤ M)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    DifferentiableAt ℂ (fun z => ∫ s in (0 : ℝ)..1, w s • G (z * (s : ℂ))) z₀ :=
  (hasDerivAt_integral_unitSegment hU hstar hG hwc hwb hz₀).differentiableAt

end GaloisForLFunctions.HTGeometry
