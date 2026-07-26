import GaloisForLFunctions.HTGeometry.HardySpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Gutzmer's identity for functions analytic on the unit disk

For a function `f` analytic on the open unit disk, the circle mean of `‖f‖²` at radius `r < 1` equals
the coefficient sum `∑ₖ ‖bₖ‖² r^{2k}` of its Taylor series (Gutzmer / Parseval on a circle).  This
generalises the `1/D`-specific machinery of `SzegoH2.lean` to an arbitrary disk-analytic function,
so it applies equally to `1/D` and to products like `Sₙ · D`.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- A function analytic on the open unit disk has a convergent power series on every closed
sub-disk. -/
theorem hasFPowerSeriesOnBall_of_analyticOnNhd_ball {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1)) {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R :=
  DifferentiableOn.hasFPowerSeriesOnBall
    (hf.differentiableOn.mono (Metric.closedBall_subset_ball hR1)) hR0

/-- The Taylor coefficients of `f` at the origin are independent of the sub-disk radius. -/
theorem cauchyPowerSeries_eq_of_analyticOnNhd_ball {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R₁ R₂ : NNReal} (h01 : 0 < R₁) (h11 : (R₁ : ℝ) < 1) (h02 : 0 < R₂) (h12 : (R₂ : ℝ) < 1) :
    cauchyPowerSeries f 0 R₁ = cauchyPowerSeries f 0 R₂ :=
  (hasFPowerSeriesOnBall_of_analyticOnNhd_ball hf h01 h11).hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesOnBall_of_analyticOnNhd_ball hf h02 h12).hasFPowerSeriesAt

/-- Uniform convergence of the Taylor partial sums of `f` composed with the circle parametrisation. -/
theorem tendstoUniformlyOn_partialSum_analytic_circleMap {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1)
    {r : ℝ} (hr0 : 0 ≤ r) {r' : NNReal} (hrr' : r < (r' : ℝ)) (hr'R : r' < R) :
    TendstoUniformlyOn
      (fun n θ => (cauchyPowerSeries f 0 R).partialSum n (circleMap 0 r θ))
      (fun θ => f (circleMap 0 r θ)) atTop Set.univ := by
  have hp := hasFPowerSeriesOnBall_of_analyticOnNhd_ball hf hR0 hR1
  have hunif := hp.tendstoUniformlyOn (r' := r') (by exact_mod_cast hr'R)
  have hcomp := hunif.comp (circleMap 0 r)
  have hset : (circleMap 0 r) ⁻¹' (Metric.ball 0 (r' : ℝ)) = Set.univ := by
    ext θ
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hr0, Set.mem_univ, iff_true]
    exact hrr'
  rw [hset] at hcomp
  refine hcomp.congr_right ?_
  intro θ _
  simp [Function.comp, zero_add]

/-- **Dominated passage to the limit for circle `L²` norms of partial sums.**  Only two facts
about the series are used: that `r` lies inside its radius of convergence — which bounds every
partial sum on the circle by the tail-summable constant `∑ ‖p n‖ r ⁿ` — and that the partial sums
converge uniformly to `f` on the circle.  Every concrete source of those two facts gives the same
conclusion. -/
theorem tendsto_integral_normSq_partialSum_of_radius_of_uniform
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ} (hr0 : 0 ≤ r)
    (hlt : (↑(r.toNNReal) : ℝ≥0∞) < p.radius)
    (huniform : TendstoUniformlyOn (fun N θ => p.partialSum N (circleMap 0 r θ))
      (fun θ => f (circleMap 0 r θ)) atTop Set.univ) :
    Tendsto (fun N => ∫ θ in (0:ℝ)..(2 * π),
        ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2)
      atTop (𝓝 (∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2)) := by
  have hs_pn : Summable (fun n => ‖p n‖ * r ^ n) := by
    have h := p.summable_norm_mul_pow hlt
    rwa [Real.coe_toNNReal r hr0] at h
  set B : ℝ := ∑' n, ‖p n‖ * r ^ n with hB
  have hnb : ∀ (N : ℕ) (θ : ℝ), ‖p.partialSum N (circleMap 0 r θ)‖ ≤ B := by
    intro N θ
    rw [FormalMultilinearSeries.partialSum]
    calc ‖∑ k ∈ Finset.range N, p k fun _ => circleMap 0 r θ‖
        ≤ ∑ k ∈ Finset.range N, ‖p k fun _ => circleMap 0 r θ‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, ‖p k‖ * r ^ k := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          calc ‖p k fun _ => circleMap 0 r θ‖
              ≤ ‖p k‖ * ∏ _i : Fin k, ‖circleMap 0 r θ‖ := (p k).le_opNorm _
            _ = ‖p k‖ * r ^ k := by
                rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                  norm_circleMap_zero, abs_of_nonneg hr0]
      _ ≤ ∑' k, ‖p k‖ * r ^ k := hs_pn.sum_le_tsum _ (fun i _ => by positivity)
      _ = B := rfl
  have hps : ∀ (N : ℕ) (z : ℂ), p.partialSum N z = ∑ k ∈ Finset.range N, p.coeff k * z ^ k := by
    intro N z
    rw [FormalMultilinearSeries.partialSum]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm])
  have hcont : ∀ N, Continuous (fun θ : ℝ => ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2) := by
    intro N
    have heq : (fun θ : ℝ => ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2)
        = fun θ : ℝ => ‖∑ k ∈ Finset.range N, p.coeff k * (circleMap 0 r θ) ^ k‖ ^ 2 := by
      funext θ; rw [hps]
    rw [heq]
    exact (continuous_finsetSum _ (fun k _ =>
      continuous_const.mul ((continuous_circleMap 0 r).pow k))).norm.pow 2
  have hgc : Continuous (fun z : ℂ => ‖z‖ ^ 2) := continuous_norm.pow 2
  have key := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc (0:ℝ) (2 * π)))
    (F := fun N θ => ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2)
    (f := fun θ => ‖f (circleMap 0 r θ)‖ ^ 2)
    (bound := fun _ => B ^ 2)
    (fun N => (hcont N).aestronglyMeasurable)
    (by
      apply integrableOn_const
      · rw [Real.volume_Ioc]; exact (ENNReal.ofReal_lt_top).ne
      · exact enorm_ne_top)
    (fun N => Eventually.of_forall (fun θ => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnb N θ) 2))
    (Eventually.of_forall (fun θ => (hgc.tendsto _).comp (huniform.tendsto_at (Set.mem_univ θ))))
  have hab : (0:ℝ) ≤ 2 * π := by positivity
  have hconv : ∀ N, (∫ θ in (0:ℝ)..(2 * π), ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2)
      = ∫ θ, ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2 ∂(volume.restrict (Set.Ioc (0:ℝ) (2 * π))) :=
    fun N => intervalIntegral.integral_of_le hab
  have hconv2 : (∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2)
      = ∫ θ, ‖f (circleMap 0 r θ)‖ ^ 2 ∂(volume.restrict (Set.Ioc (0:ℝ) (2 * π))) :=
    intervalIntegral.integral_of_le hab
  rw [hconv2]
  simp only [hconv]

/-- Dominated convergence of the partial-sum circle integrals to the integral of `‖f‖²`. -/
theorem tendsto_integral_normSq_partialSum_analytic {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hrR : r < (R : ℝ)) :
    Tendsto (fun N => ∫ θ in (0:ℝ)..(2 * π),
        ‖(cauchyPowerSeries f 0 R).partialSum N (circleMap 0 r θ)‖ ^ 2)
      atTop (𝓝 (∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2)) := by
  have hp := hasFPowerSeriesOnBall_of_analyticOnNhd_ball hf hR0 hR1
  have hlt : (↑(r.toNNReal) : ℝ≥0∞) < (cauchyPowerSeries f 0 R).radius := by
    refine lt_of_lt_of_le ?_ hp.r_le
    rw [ENNReal.coe_lt_coe]
    exact NNReal.coe_lt_coe.mp (by rw [Real.coe_toNNReal r hr0]; exact hrR)
  obtain ⟨x, hrx, hxR⟩ := exists_between hrR
  have hxpos : 0 ≤ x := le_of_lt (lt_of_le_of_lt hr0 hrx)
  exact tendsto_integral_normSq_partialSum_of_radius_of_uniform hr0 hlt
    (tendstoUniformlyOn_partialSum_analytic_circleMap hf hR0 hR1 hr0
      (r' := x.toNNReal) (by rw [Real.coe_toNNReal x hxpos]; exact hrx)
      (NNReal.coe_lt_coe.mp (by rw [Real.coe_toNNReal x hxpos]; exact hxR)))
  exact key

/-- **Gutzmer's identity (limit form).**  For `f` analytic on the disk and `r < R < 1`, the partial
coefficient sums `∑_{k<N} ‖bₖ‖² r^{2k}` converge to the circle mean `(2π)⁻¹∫₀²π ‖f(re^{iθ})‖²`. -/
theorem tendsto_gutzmer_partialSum {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hrR : r < (R : ℝ)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k))
      atTop (𝓝 ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2)) := by
  have h := (tendsto_integral_normSq_partialSum_analytic hf hR0 hR1 hr0 hrR).const_mul ((2 * π)⁻¹)
  simpa only [circleAverage_normSq_partialSum (cauchyPowerSeries f 0 R) r] using h

/-- **Gutzmer's identity (sum form).**  The circle mean of `‖f‖²` at radius `r` is the Taylor
coefficient sum `∑ₖ ‖bₖ‖² r^{2k}`. -/
theorem hasSum_gutzmer {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hrR : r < (R : ℝ)) :
    HasSum (fun k => ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k))
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by
  have htend := tendsto_gutzmer_partialSum hf hR0 hR1 hr0 hrR
  have hmono : Monotone (fun N =>
      ∑ k ∈ Finset.range N, ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [Finset.sum_range_succ]
    have : 0 ≤ ‖(cauchyPowerSeries f 0 R).coeff n‖ ^ 2 * r ^ (2 * n) := by positivity
    linarith
  have hsummable : Summable (fun k => ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)) :=
    summable_of_sum_range_le (fun n => by positivity) (fun n => hmono.ge_of_tendsto htend n)
  have hts := hsummable.hasSum
  rwa [tendsto_nhds_unique hsummable.hasSum.tendsto_sum_nat htend] at hts

end GaloisForLFunctions.HTGeometry
