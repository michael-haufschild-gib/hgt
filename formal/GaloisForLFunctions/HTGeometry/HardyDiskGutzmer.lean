import GaloisForLFunctions.HTGeometry.HardySpace

/-!
# Gutzmer's identity on the disk

`hardy-cyclicity-maximal-ht-field-blindness`, analytic substrate.

For a function with a power series on a ball of radius `R` centred at `0`, and every `r < R`,

```text
(2π)⁻¹ ∫₀²π ‖f(r e^{iθ})‖² dθ = ∑ₖ ‖aₖ‖² r^{2k}.
```

`circleAverage_normSq_partialSum` gives the finite version; this module passes to the limit using
the uniform convergence of the partial sums on a slightly larger ball.  The identity is the whole
analytic content of the Hardy-space norm: it turns the boundary `L²` estimate into a statement
about Taylor coefficients.
-/

open Complex Filter Metric Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem circleMap_mem_ball {r : ℝ} {r' : NNReal} (hr0 : 0 ≤ r) (hrr' : r < r') (θ : ℝ) :
    circleMap 0 r θ ∈ Metric.ball (0 : ℂ) r' := by
  rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
  exact hrr'

/-- **Gutzmer's identity.**  The circle average of `‖f‖²` at radius `r` is the weighted
coefficient sum. -/
theorem hasSum_circleAverage_normSq
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ENNReal}
    (hf : HasFPowerSeriesOnBall f p 0 R) {r : ℝ} {r' : NNReal}
    (hr0 : 0 ≤ r) (hrr' : r < r') (hr'R : (r' : ENNReal) < R) :
    HasSum (fun k => ‖p.coeff k‖ ^ 2 * r ^ (2 * k))
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by
  have hπ : (0:ℝ) < 2 * π := by positivity
  have huc : TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (0 + y)) atTop
      (Metric.ball (0 : ℂ) r') := hf.tendstoUniformlyOn hr'R
  have hucz : TendstoUniformlyOn (fun n y => p.partialSum n y) f atTop
      (Metric.ball (0 : ℂ) r') := by
    refine huc.congr_right fun y _ => ?_
    show f (0 + y) = f y
    rw [zero_add]
  -- continuity of the limit on the circle
  have hfcont : ContinuousOn f (Metric.ball (0 : ℂ) r') := by
    refine hucz.continuousOn ?_
    exact (Filter.Eventually.of_forall
      fun n => (p.partialSum_continuous n).continuousOn).frequently
  have hcircle : Continuous (fun θ : ℝ => circleMap 0 r θ) := continuous_circleMap 0 r
  have hgcont : ContinuousOn (fun θ : ℝ => ‖f (circleMap 0 r θ)‖ ^ 2) (Set.Icc 0 (2 * π)) := by
    refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
    exact hfcont.comp hcircle.continuousOn (fun θ _ => circleMap_mem_ball hr0 hrr' θ)
  have hFcont : ContinuousOn (fun θ : ℝ => f (circleMap 0 r θ)) (Set.Icc 0 (2 * π)) :=
    hfcont.comp hcircle.continuousOn (fun θ _ => circleMap_mem_ball hr0 hrr' θ)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hFcont
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, by positivity⟩)
  -- integrability
  have hgint : IntervalIntegrable (fun θ : ℝ => ‖f (circleMap 0 r θ)‖ ^ 2) MeasureTheory.volume
      0 (2 * π) := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 2 * π)]
  have hSint : ∀ N : ℕ, IntervalIntegrable
      (fun θ : ℝ => ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2) MeasureTheory.volume 0 (2 * π) :=
    fun N => (((p.partialSum_continuous N).comp hcircle).norm.pow 2).intervalIntegrable _ _
  -- the integrals converge
  have hconv : Tendsto
      (fun N => ∫ θ in (0:ℝ)..(2 * π), ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2) atTop
      (𝓝 (∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ : ℝ := min 1 (ε / (2 * (2 * C + 1) * (2 * π))) with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      refine lt_min one_pos ?_
      positivity
    obtain ⟨N₀, hN₀⟩ := (Metric.tendstoUniformlyOn_iff.mp hucz) δ hδpos |>.exists_forall_of_atTop
    refine ⟨N₀, fun N hN => ?_⟩
    have hbound : ∀ θ ∈ Set.uIoc (0:ℝ) (2 * π),
        ‖‖p.partialSum N (circleMap 0 r θ)‖ ^ 2 - ‖f (circleMap 0 r θ)‖ ^ 2‖
          ≤ (2 * C + 1) * δ := by
      intro θ hθ
      have hθIcc : θ ∈ Set.Icc (0:ℝ) (2 * π) := by
        rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * π)] at hθ
        exact ⟨le_of_lt hθ.1, hθ.2⟩
      have hd := hN₀ N hN (circleMap 0 r θ) (circleMap_mem_ball hr0 hrr' θ)
      rw [dist_eq_norm] at hd
      have hd' : ‖p.partialSum N (circleMap 0 r θ) - f (circleMap 0 r θ)‖ ≤ δ := by
        have : ‖f (circleMap 0 r θ) - p.partialSum N (circleMap 0 r θ)‖ ≤ δ := le_of_lt hd
        rwa [norm_sub_rev] at this
      have hfC : ‖f (circleMap 0 r θ)‖ ≤ C := hC θ hθIcc
      have hSC : ‖p.partialSum N (circleMap 0 r θ)‖ ≤ C + δ := by
        have := norm_sub_norm_le (p.partialSum N (circleMap 0 r θ)) (f (circleMap 0 r θ))
        linarith [hd', hfC]
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have habs : ‖‖p.partialSum N (circleMap 0 r θ)‖ ^ 2 - ‖f (circleMap 0 r θ)‖ ^ 2‖
          = |‖p.partialSum N (circleMap 0 r θ)‖ ^ 2 - ‖f (circleMap 0 r θ)‖ ^ 2| :=
        Real.norm_eq_abs _
      rw [habs, abs_le]
      have hSnn : (0:ℝ) ≤ ‖p.partialSum N (circleMap 0 r θ)‖ := norm_nonneg _
      have hfnn : (0:ℝ) ≤ ‖f (circleMap 0 r θ)‖ := norm_nonneg _
      have hdiff : |‖p.partialSum N (circleMap 0 r θ)‖ - ‖f (circleMap 0 r θ)‖| ≤ δ := by
        rw [abs_sub_le_iff]
        constructor
        · have := norm_sub_norm_le (p.partialSum N (circleMap 0 r θ)) (f (circleMap 0 r θ))
          linarith
        · have := norm_sub_norm_le (f (circleMap 0 r θ)) (p.partialSum N (circleMap 0 r θ))
          rw [norm_sub_rev] at this
          linarith
      rw [abs_le] at hdiff
      constructor <;> nlinarith [hdiff.1, hdiff.2, hSnn, hfnn, hfC, hSC, hδpos.le, hδ1, hC0]
    have hsub : ‖(∫ θ in (0:ℝ)..(2 * π), ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2)
        - ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2‖ ≤ (2 * C + 1) * δ * |2 * π - 0| := by
      rw [← intervalIntegral.integral_sub (hSint N) hgint]
      exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [dist_eq_norm]
    have hδle : δ ≤ ε / (2 * (2 * C + 1) * (2 * π)) := min_le_right _ _
    have hCpos : (0:ℝ) < 2 * C + 1 := by linarith
    have hstep : (2 * C + 1) * δ * |2 * π - 0| ≤ ε / 2 := by
      rw [sub_zero, abs_of_pos hπ]
      have h1 : (2 * C + 1) * δ ≤ (2 * C + 1) * (ε / (2 * (2 * C + 1) * (2 * π))) :=
        mul_le_mul_of_nonneg_left hδle (le_of_lt hCpos)
      have h2 : (2 * C + 1) * (ε / (2 * (2 * C + 1) * (2 * π))) * (2 * π) = ε / 2 := by
        field_simp
      nlinarith [h1, hπ.le, h2]
    linarith [hsub, hstep]
  -- transfer to the coefficient sums
  have hpartial : Tendsto
      (fun N => ∑ k ∈ Finset.range N, ‖p.coeff k‖ ^ 2 * r ^ (2 * k)) atTop
      (𝓝 ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2)) := by
    have h := hconv.const_mul ((2 * π)⁻¹)
    refine h.congr fun N => ?_
    exact (circleAverage_normSq_partialSum p r N)
  have hnn : ∀ k : ℕ, 0 ≤ ‖p.coeff k‖ ^ 2 * r ^ (2 * k) := by
    intro k; positivity
  have hsummable : Summable (fun k => ‖p.coeff k‖ ^ 2 * r ^ (2 * k)) := by
    refine summable_of_sum_range_le hnn (c := (2 * π)⁻¹ *
      ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) fun n => ?_
    refine ge_of_tendsto hpartial ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      (fun i _ _ => hnn i)
  exact (hsummable.hasSum_iff_tendsto_nat).mpr hpartial

end GaloisForLFunctions.HTGeometry
