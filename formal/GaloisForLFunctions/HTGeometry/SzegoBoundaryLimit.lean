import GaloisForLFunctions.HTGeometry.SzegoRadialMean

/-!
# The interior circle mean converges to the boundary integral

For a continuous multiplier `g` and the outer function `D` of a positive bounded weight `w`, the
radial circle mean `circleMeanSq (g · D) r` converges, as `r → 1⁻`, to the boundary integral
`(2π)⁻¹∫₀²π ‖g(e^{iθ})‖² w(θ)`.  This is dominated convergence: `‖D(re^{iθ})‖² → w(θ)` a.e. and is
bounded by `C`, while `g(re^{iθ}) → g(e^{iθ})`.  This is the bridge that turns interior coefficient
estimates into control of the boundary Szegő integral.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- **Boundary limit of the interior mean.**  `circleMeanSq (g·D) r → (2π)⁻¹∫ ‖g(e^{iθ})‖² w` as
`r → 1⁻`. -/
theorem tendsto_circleMeanSq_mul_szegoOuter {g : ℂ → ℂ} (hgc : Continuous g)
    {w : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hlogLI : LocallyIntegrable (fun θ => Real.log (w θ)) volume)
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwpos : ∀ θ, 0 < w θ) (hwC : ∀ θ, w θ ≤ C) :
    Tendsto (fun r => circleMeanSq (fun z => g z * szegoOuter w z) r) (𝓝[<] 1)
      (𝓝 ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖g (circleMap 0 1 θ)‖ ^ 2 * w θ)) := by
  -- bound on `g` over the closed disk
  obtain ⟨z₀, _, hz₀max⟩ := (isCompact_closedBall (0:ℂ) 1).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hgc.norm.continuousOn
  set Mg : ℝ := ‖g z₀‖ with hMg
  have hMg0 : 0 ≤ Mg := norm_nonneg _
  have hgbound : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → ∀ θ, ‖g (circleMap 0 r θ)‖ ≤ Mg := by
    intro r hr0 hr1 θ
    refine hz₀max ?_
    rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]; exact hr1
  set μ := volume.restrict (Set.Ioc (0:ℝ) (2 * π))
  set F : ℝ → ℝ → ℝ := fun r θ => ‖g (circleMap 0 r θ) * szegoOuter w (circleMap 0 r θ)‖ ^ 2 with hF
  set flim : ℝ → ℝ := fun θ => ‖g (circleMap 0 1 θ)‖ ^ 2 * w θ with hflim
  have hab : (0:ℝ) ≤ 2 * π := by positivity
  -- eventual `0 < r`
  have h0r : ∀ᶠ r in 𝓝[<] (1:ℝ), (0:ℝ) < r :=
    ((isOpen_Ioi.eventually_mem (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
  have hr1 : ∀ᶠ r in 𝓝[<] (1:ℝ), r < 1 :=
    eventually_nhdsWithin_of_forall (fun r hr => hr)
  -- measurability
  have hFmeas : ∀ᶠ r in 𝓝[<] (1:ℝ), AEStronglyMeasurable (F r) μ := by
    filter_upwards [h0r, hr1] with r hr0 hr1v
    have hDc : Continuous (fun θ : ℝ => szegoOuter w (circleMap 0 r θ)) := by
      have hin : ∀ θ, circleMap 0 r θ ∈ Metric.ball (0:ℂ) 1 := by
        intro θ
        rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0.le]; exact hr1v
      exact (analyticOnNhd_szegoOuter hlog).continuousOn.comp_continuous
        (continuous_circleMap 0 r) hin
    exact (((hgc.comp (continuous_circleMap 0 r)).mul hDc).norm.pow 2).aestronglyMeasurable
  -- domination
  have hbound : ∀ᶠ r in 𝓝[<] (1:ℝ), ∀ᵐ θ ∂μ, ‖F r θ‖ ≤ Mg ^ 2 * C := by
    filter_upwards [h0r, hr1] with r hr0 hr1v
    refine Eventually.of_forall (fun θ => ?_)
    simp only [hF]
    rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
    have hD := normSq_szegoOuter_le hC hlog hper hlogφ hwpos hwC hr0.le hr1v θ
    have hg := hgbound hr0.le hr1v.le θ
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hg 2) hD (by positivity) (by positivity)
  have hboundInt : Integrable (fun _ => Mg ^ 2 * C) μ := by
    apply integrableOn_const
    · rw [Real.volume_Ioc]; exact (ENNReal.ofReal_lt_top).ne
    · exact enorm_ne_top
  -- pointwise limit a.e.
  have hlim : ∀ᵐ θ ∂μ, Tendsto (fun r => F r θ) (𝓝[<] 1) (𝓝 (flim θ)) := by
    have hae := tendsto_normSq_szegoOuter_ae hlogLI hlog hper hwpos
    rw [hF, hflim] at *
    filter_upwards [ae_restrict_of_ae hae] with θ hθ
    have hz : Tendsto (fun r : ℝ => circleMap 0 r θ) (𝓝[<] 1) (𝓝 (circleMap 0 1 θ)) := by
      have : Continuous (fun r : ℝ => circleMap 0 r θ) := by
        simp only [circleMap]; fun_prop
      exact (this.tendsto 1).mono_left nhdsWithin_le_nhds
    have hgt : Tendsto (fun r : ℝ => ‖g (circleMap 0 r θ)‖ ^ 2) (𝓝[<] 1)
        (𝓝 (‖g (circleMap 0 1 θ)‖ ^ 2)) :=
      ((hgc.norm.pow 2).tendsto (circleMap 0 1 θ)).comp hz
    have hmul := hgt.mul hθ
    refine hmul.congr (fun r => ?_)
    rw [norm_mul, mul_pow]
  have key := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[<] (1:ℝ))
    (F := F) (f := flim) (fun _ => Mg ^ 2 * C) hFmeas hbound hboundInt hlim
  -- convert to interval integrals and multiply by `(2π)⁻¹`
  have hconvF : ∀ r, (∫ θ in (0:ℝ)..(2 * π), F r θ) = ∫ θ, F r θ ∂μ :=
    fun r => intervalIntegral.integral_of_le hab
  have hconvf : (∫ θ in (0:ℝ)..(2 * π), flim θ) = ∫ θ, flim θ ∂μ :=
    intervalIntegral.integral_of_le hab
  have key2 : Tendsto (fun r => ∫ θ in (0:ℝ)..(2 * π), F r θ) (𝓝[<] 1)
      (𝓝 (∫ θ in (0:ℝ)..(2 * π), flim θ)) := by
    rw [hconvf]; simp only [hconvF]; exact key
  exact key2.const_mul ((2 * π)⁻¹)

end GaloisForLFunctions.HTGeometry
