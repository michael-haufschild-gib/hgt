import GaloisForLFunctions.HTGeometry.HardyTaylorCoefficient

/-!
# Circle means of disk-analytic functions

This module proves the complex mean-value identity directly from the Cauchy power series.  The
interval-integral form is convenient for Hardy-class estimates built from analytic exponentials.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem integral_circleMap_eq_center_of_lt_radius {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hrR : r < (R : ℝ)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 r θ)) =
      (2 * Real.pi : ℂ) * f 0 := by
  let p := cauchyPowerSeries f 0 R
  have hp := hasFPowerSeriesOnBall_of_analyticOnNhd_ball hf hR0 hR1
  have hlt : (↑(r.toNNReal) : ℝ≥0∞) < p.radius := by
    refine lt_of_lt_of_le ?_ hp.r_le
    rw [ENNReal.coe_lt_coe]
    exact NNReal.coe_lt_coe.mp (by rw [Real.coe_toNNReal r hr0]; exact hrR)
  have hs : Summable (fun n => ‖p n‖ * r ^ n) := by
    have h := p.summable_norm_mul_pow hlt
    rwa [Real.coe_toNNReal r hr0] at h
  let B : ℝ := ∑' n, ‖p n‖ * r ^ n
  have hbound : ∀ (N : ℕ) (θ : ℝ),
      ‖p.partialSum N (circleMap 0 r θ)‖ ≤ B := by
    intro N θ
    rw [FormalMultilinearSeries.partialSum]
    calc
      ‖∑ k ∈ Finset.range N, p k fun _ => circleMap 0 r θ‖ ≤
          ∑ k ∈ Finset.range N, ‖p k fun _ => circleMap 0 r θ‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, ‖p k‖ * r ^ k := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        calc
          ‖p k fun _ => circleMap 0 r θ‖ ≤
              ‖p k‖ * ∏ _i : Fin k, ‖circleMap 0 r θ‖ := (p k).le_opNorm _
          _ = ‖p k‖ * r ^ k := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              norm_circleMap_zero, abs_of_nonneg hr0]
      _ ≤ ∑' k, ‖p k‖ * r ^ k := hs.sum_le_tsum _ (fun i _ => by positivity)
      _ = B := rfl
  obtain ⟨r', hrr', hr'R⟩ := exists_between hrR
  have hr'0 : 0 ≤ r' := hr0.trans (le_of_lt hrr')
  have huniform := tendstoUniformlyOn_partialSum_analytic_circleMap
    hf hR0 hR1 hr0 (r' := r'.toNNReal)
      (by rw [Real.coe_toNNReal r' hr'0]; exact hrr')
      (NNReal.coe_lt_coe.mp (by rw [Real.coe_toNNReal r' hr'0]; exact hr'R))
  have hcont : ∀ N, Continuous (fun θ : ℝ =>
      p.partialSum N (circleMap 0 r θ)) := by
    intro N
    exact (p.partialSum_continuous N).comp (continuous_circleMap 0 r)
  have hintTendsto : Tendsto
      (fun N => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        p.partialSum N (circleMap 0 r θ)) atTop
      (𝓝 (∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 r θ))) := by
    have hdc := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
      (F := fun N θ => p.partialSum N (circleMap 0 r θ))
      (f := fun θ => f (circleMap 0 r θ))
      (bound := fun _ => B)
      (fun N => (hcont N).aestronglyMeasurable)
      (by
        apply integrableOn_const
        · rw [Real.volume_Ioc]
          exact (ENNReal.ofReal_lt_top).ne
        · exact enorm_ne_top)
      (fun N => Eventually.of_forall fun θ => hbound N θ)
      (Eventually.of_forall fun θ => huniform.tendsto_at (Set.mem_univ θ))
    simpa only [intervalIntegral.integral_of_le (by positivity :
      (0 : ℝ) ≤ 2 * Real.pi)] using hdc
  have hmonomial (k : ℕ) :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 r θ) ^ k) =
        if k = 0 then (2 * Real.pi : ℂ) else 0 := by
    rw [show (∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 r θ) ^ k) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (circleMap 0 r θ) ^ k *
            (starRingEnd ℂ) ((circleMap 0 r θ) ^ 0) by simp]
    rw [integral_circleMap_pow_conj]
    split_ifs with hk
    · subst k
      simp
    · rfl
  have hp0 : p.coeff 0 = f 0 := by
    have heq : cauchyPowerSeries f 0 R =
        cauchyPowerSeries f 0 (1 / 2 : NNReal) :=
      cauchyPowerSeries_eq_of_analyticOnNhd_ball hf hR0 hR1
        (by norm_num) (by norm_num)
    change (cauchyPowerSeries f 0 R).coeff 0 = f 0
    rw [heq, cauchyPowerSeries_coeff_eq_iteratedDeriv_div_factorial hf 0]
    simp
  have hps : ∀ (N : ℕ) (z : ℂ), p.partialSum N z =
      ∑ k ∈ Finset.range N, p.coeff k * z ^ k := by
    intro N z
    rw [FormalMultilinearSeries.partialSum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  have hpartial : ∀ N, 0 < N →
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        p.partialSum N (circleMap 0 r θ)) =
          (2 * Real.pi : ℂ) * f 0 := by
    intro N hN
    simp_rw [hps]
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, hmonomial]
      rw [Finset.sum_eq_single 0]
      · simp [hp0, mul_comm]
      · intro b hb hne
        simp [hne]
      · simp [hN]
    · intro k hk
      exact (continuous_const.mul ((continuous_circleMap 0 r).pow k)).intervalIntegrable _ _
  have hconst : Tendsto (fun _ : ℕ => (2 * Real.pi : ℂ) * f 0)
      atTop (𝓝 ((2 * Real.pi : ℂ) * f 0)) := tendsto_const_nhds
  have heq : (fun N => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      p.partialSum N (circleMap 0 r θ)) =ᶠ[atTop]
        fun _ => (2 * Real.pi : ℂ) * f 0 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact hpartial N hN
  exact tendsto_nhds_unique hintTendsto (hconst.congr' heq.symm)

/-- The integral of a complex function analytic near the open unit disk over every centered circle
of radius below one is its central value times the angular length. -/
theorem integral_circleMap_eq_center_of_analyticOnNhd_unitBall {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 r θ)) =
      (2 * Real.pi : ℂ) * f 0 := by
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  have hR0 : 0 < R := hr0.trans_lt hrR
  exact integral_circleMap_eq_center_of_lt_radius hf
    (R := R.toNNReal)
    (by simpa [Real.toNNReal_pos])
    (by simpa [Real.coe_toNNReal R (le_of_lt hR0)])
    hr0
    (by simpa [Real.coe_toNNReal R (le_of_lt hR0)])

end

end GaloisForLFunctions.HTGeometry
