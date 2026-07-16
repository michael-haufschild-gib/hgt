import GaloisForLFunctions.HTGeometry.SzegoRadialMean

open MeasureTheory Complex Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Radial circle integrals of a function continuous on the closed unit disk converge to its
boundary circle integral as the radius tends to one from below. -/
theorem tendsto_intervalIntegral_circleMap_radius_of_continuousOn
    {F : ℂ → ℝ} (hF : ContinuousOn F (Metric.closedBall 0 1)) :
    Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), F (circleMap 0 r θ))
      (𝓝[<] 1) (𝓝 (∫ θ in (0 : ℝ)..(2 * π), F (circleMap 0 1 θ))) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hF.norm
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => C)
  · filter_upwards [hIoo] with r hr
    exact (hF.comp_continuous (continuous_circleMap 0 r) (fun θ => by
      rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg hr.1.le]
      exact hr.2.le)).aestronglyMeasurable
  · filter_upwards [hIoo] with r hr
    filter_upwards [] with θ hθ
    rw [Real.norm_eq_abs]
    apply hC
    refine ⟨circleMap 0 r θ, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hr.1.le]
    exact hr.2.le
  · exact intervalIntegrable_const
  · filter_upwards [] with θ hθ
    have hmap : Tendsto (fun r : ℝ => circleMap 0 r θ) (𝓝[<] 1)
        (𝓝[Metric.closedBall (0 : ℂ) 1] (circleMap 0 1 θ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hc : Continuous (fun r : ℝ => circleMap 0 r θ) := by fun_prop
        exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [hIoo] with r hr
        rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero,
          abs_of_nonneg hr.1.le]
        exact hr.2.le
    exact Filter.Tendsto.comp (hF (circleMap 0 1 θ) (by
      rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero]
      norm_num)) hmap

/-- A finite boundary limit for radial `L²` means makes the Taylor coefficient sequence square
summable, with the exact same upper bound. -/
theorem cauchyPowerSeries_coeff_memℓp_two_of_circleMeanSq_tendsto
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1)) {M : ℝ}
    (hlim : Tendsto (circleMeanSq f) (𝓝[<] (1 : ℝ)) (𝓝 M)) :
    Memℓp (fun k => (cauchyPowerSeries f 0 (1 / 2 : NNReal)).coeff k) 2 ∧
      ∑' k, ‖(cauchyPowerSeries f 0 (1 / 2 : NNReal)).coeff k‖ ^ 2 ≤ M := by
  have hR0 : (0 : NNReal) < 1 / 2 := by norm_num
  have hR1 : ((1 / 2 : NNReal) : ℝ) < 1 := by norm_num
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
  have hstep : ∀ N, ∑ k ∈ Finset.range N,
      ‖(cauchyPowerSeries f 0 (1 / 2 : NNReal)).coeff k‖ ^ 2 ≤ M := by
    intro N
    let φ : ℝ → ℝ := fun r => ∑ k ∈ Finset.range N,
      ‖(cauchyPowerSeries f 0 (1 / 2 : NNReal)).coeff k‖ ^ 2 * r ^ (2 * k)
    have hφcont : Continuous φ := by
      dsimp [φ]
      exact continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_pow (2 * k)))
    have hφlim : Tendsto φ (𝓝[<] (1 : ℝ)) (𝓝 (φ 1)) :=
      (hφcont.tendsto 1).mono_left nhdsWithin_le_nhds
    have hle : ∀ᶠ r in 𝓝[<] (1 : ℝ), φ r ≤ circleMeanSq f r := by
      filter_upwards [hIoo] with r hr
      exact sum_range_le_circleMeanSq hf hR0 hR1 hr.1.le hr.2 N
    have hφ1 : φ 1 ≤ M := le_of_tendsto_of_tendsto hφlim hlim hle
    simpa [φ] using hφ1
  have hsum : Summable (fun k =>
      ‖(cauchyPowerSeries f 0 (1 / 2 : NNReal)).coeff k‖ ^ 2) :=
    summable_of_sum_range_le (fun k => by positivity) hstep
  constructor
  · apply memℓp_gen
    simpa using hsum
  · exact Real.tsum_le_of_sum_range_le (fun k => by positivity) hstep

end
end GaloisForLFunctions.HTGeometry
