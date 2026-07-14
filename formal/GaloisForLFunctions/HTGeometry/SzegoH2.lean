import GaloisForLFunctions.HTGeometry.SzegoOuterAnalytic
import GaloisForLFunctions.HTGeometry.SzegoOuterBoundary
import GaloisForLFunctions.HTGeometry.HardySpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The reciprocal outer function lies in `H²`

For a weight `w` bounded below by `c > 0`, the reciprocal Szegő outer function `1/D` has
square-summable Taylor coefficients with `∑ ‖bₖ‖² ≤ c⁻¹`.  This is the analytic heart of the Szegő
upper bound: it is what makes the reversed Taylor polynomials of `D(0)/D` a valid approximating
family in the extremal minimization.

The proof is Gutzmer's identity at radius `r < 1`, `∑_{k<N} ‖bₖ‖² r^{2k} = (2π)⁻¹∫₀²π‖1/D(re^{iθ})‖²`,
combined with the pointwise disk bound `‖1/D‖² ≤ c⁻¹` and the limit `r → 1`.  The radius-`r`
identity itself comes from dominated convergence of the Taylor partial sums.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real ComplexConjugate ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- **Coefficient independence.**  The Cauchy/Taylor coefficients of `1/D` at the origin do not
depend on the radius of the disk on which they are computed — they are the unique power-series
coefficients.  This lets a single coefficient sequence carry the radius-`r` Gutzmer identities as
`r → 1`. -/
theorem cauchyPowerSeries_inv_szegoOuter_eq {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {R₁ R₂ : NNReal} (h01 : 0 < R₁) (h11 : (R₁ : ℝ) < 1) (h02 : 0 < R₂) (h12 : (R₂ : ℝ) < 1) :
    cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₁
      = cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₂ :=
  (hasFPowerSeriesOnBall_inv_szegoOuter hlog h01 h11).hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesOnBall_inv_szegoOuter hlog h02 h12).hasFPowerSeriesAt

/-- **Dominated convergence of the Taylor partial sums.**  For `r < R < 1`, the integrals of
`‖Sₙ(re^{iθ})‖²` over `[0,2π]` converge to the integral of `‖1/D(re^{iθ})‖²`.  The dominating
constant is `B² = (∑ₙ ‖pₙ‖ rⁿ)²`, finite because `r` is inside the disk of convergence. -/
theorem tendsto_integral_normSq_partialSum {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hrR : r < (R : ℝ)) :
    Tendsto (fun N => ∫ θ in (0:ℝ)..(2 * π),
        ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R).partialSum N (circleMap 0 r θ)‖ ^ 2)
      atTop (𝓝 (∫ θ in (0:ℝ)..(2 * π), ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2)) := by
  set p := cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R with hp_def
  have hp := hasFPowerSeriesOnBall_inv_szegoOuter hlog hR0 hR1
  -- `r` lies inside the disk of convergence
  have hlt : (↑(r.toNNReal) : ℝ≥0∞) < p.radius := by
    refine lt_of_lt_of_le ?_ hp.r_le
    rw [ENNReal.coe_lt_coe]
    exact NNReal.coe_lt_coe.mp (by rw [Real.coe_toNNReal r hr0]; exact hrR)
  have hs_pn : Summable (fun n => ‖p n‖ * r ^ n) := by
    have h := p.summable_norm_mul_pow hlt
    rwa [Real.coe_toNNReal r hr0] at h
  set B : ℝ := ∑' n, ‖p n‖ * r ^ n with hB
  -- uniform pointwise bound on the partial sums
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
  -- continuity of the integrand (for measurability)
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
  -- pointwise limit from the banked uniform convergence
  obtain ⟨x, hrx, hxR⟩ := exists_between hrR
  have hxpos : 0 ≤ x := le_of_lt (lt_of_le_of_lt hr0 hrx)
  have huniform := tendstoUniformlyOn_partialSum_inv_szegoOuter_circleMap hlog hR0 hR1 hr0
    (r' := x.toNNReal) (by rw [Real.coe_toNNReal x hxpos]; exact hrx)
    (NNReal.coe_lt_coe.mp (by rw [Real.coe_toNNReal x hxpos]; exact hxR))
  have hgc : Continuous (fun z : ℂ => ‖z‖ ^ 2) := continuous_norm.pow 2
  have key := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc (0:ℝ) (2 * π)))
    (F := fun N θ => ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2)
    (f := fun θ => ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2)
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
  have hconv2 : (∫ θ in (0:ℝ)..(2 * π), ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2)
      = ∫ θ, ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2 ∂(volume.restrict (Set.Ioc (0:ℝ) (2 * π))) :=
    intervalIntegral.integral_of_le hab
  rw [hconv2]
  simp only [hconv]
  exact key

/-- **Gutzmer inequality at radius `r`.**  For a weight bounded below by `c > 0`, every partial sum
`∑_{k<N} ‖bₖ‖² r^{2k}` of the reciprocal outer function's coefficients is `≤ c⁻¹`, uniformly in
`r < 1`.  The bound is the pointwise disk estimate `‖1/D‖² ≤ c⁻¹` pushed through Gutzmer's
identity. -/
theorem gutzmer_partialSum_le {w : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwc : ∀ θ, c ≤ w θ)
    {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hrR : r < (R : ℝ)) (N : ℕ) :
    ∑ k ∈ Finset.range N,
        ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R).coeff k‖ ^ 2 * r ^ (2 * k)
      ≤ c⁻¹ := by
  have hr1 : r < 1 := lt_trans hrR hR1
  have htend_int := tendsto_integral_normSq_partialSum hlog hR0 hR1 hr0 hrR
  set p := cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R with hp_def
  have htend : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖p.coeff k‖ ^ 2 * r ^ (2 * k))
      atTop (𝓝 ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
        ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2)) := by
    have h := htend_int.const_mul ((2 * π)⁻¹)
    simpa only [circleAverage_normSq_partialSum p r] using h
  -- the limit is `≤ c⁻¹`
  have hpi : (0:ℝ) < 2 * π := by positivity
  have hcont_g : Continuous (fun θ : ℝ => ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2) := by
    have hcircle_in : ∀ θ, circleMap 0 r θ ∈ Metric.ball (0:ℂ) 1 := by
      intro θ
      rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
      exact hr1
    exact (((analyticOnNhd_inv_szegoOuter hlog).continuousOn).comp_continuous
      (continuous_circleMap 0 r) hcircle_in).norm.pow 2
  have hbound : (∫ θ in (0:ℝ)..(2 * π), ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2)
      ≤ ∫ θ in (0:ℝ)..(2 * π), c⁻¹ := by
    apply intervalIntegral.integral_mono_on hpi.le
    · exact hcont_g.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · intro θ _
      exact normSq_inv_szegoOuter_le hc hlog hper hlogφ hwc hr0 hr1 θ
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hbound
  have hL : (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2 ≤ c⁻¹ := by
    calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖(szegoOuter w (circleMap 0 r θ))⁻¹‖ ^ 2
        ≤ (2 * π)⁻¹ * (2 * π * c⁻¹) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = c⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]
  have hmono : Monotone (fun N => ∑ k ∈ Finset.range N, ‖p.coeff k‖ ^ 2 * r ^ (2 * k)) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [Finset.sum_range_succ]
    have : 0 ≤ ‖p.coeff n‖ ^ 2 * r ^ (2 * n) := by positivity
    linarith
  exact le_trans (hmono.ge_of_tendsto htend N) hL

/-- **The reciprocal outer function is in `H²`.**  For a weight bounded below by `c > 0`, the sums
`∑_{k<N} ‖bₖ‖²` of the reciprocal outer function's squared Taylor coefficients are all `≤ c⁻¹`.
This is the radius-`1` limit of the Gutzmer inequality, and states `1/D ∈ H²` with
`‖1/D‖²_{H²} ≤ c⁻¹`. -/
theorem gutzmer_tsum_le {w : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwc : ∀ θ, c ≤ w θ)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N,
        ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2 ≤ c⁻¹ := by
  set φ : ℝ → ℝ := fun r => ∑ k ∈ Finset.range N,
      ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k) with hφ
  have hφcont : Continuous φ := by
    rw [hφ]
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_pow (2 * k)))
  have hφle : ∀ r ∈ Set.Ioo (0:ℝ) 1, φ r ≤ c⁻¹ := by
    intro r hr
    obtain ⟨s, hrs, hs1⟩ := exists_between hr.2
    have hs0 : (0:ℝ) ≤ s := le_of_lt (lt_trans hr.1 hrs)
    have hSpos : 0 < s.toNNReal := Real.toNNReal_pos.mpr (lt_trans hr.1 hrs)
    have hS1 : (s.toNNReal : ℝ) < 1 := by rw [Real.coe_toNNReal s hs0]; exact hs1
    have hrS : r < (s.toNNReal : ℝ) := by rw [Real.coe_toNNReal s hs0]; exact hrs
    have hbound := gutzmer_partialSum_le hc hlog hper hlogφ hwc hSpos hS1 (le_of_lt hr.1) hrS N
    have heq := cauchyPowerSeries_inv_szegoOuter_eq hlog hSpos hS1 hR₀0 hR₀1
    rw [show φ r = ∑ k ∈ Finset.range N,
        ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 s.toNNReal).coeff k‖ ^ 2 * r ^ (2 * k)
        from by simp only [hφ, ← heq]]
    exact hbound
  have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
  have hlim : Tendsto φ (𝓝[<] (1:ℝ)) (𝓝 (φ 1)) := (hφcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hφ1 : φ 1 ≤ c⁻¹ := le_of_tendsto hlim (Filter.eventually_of_mem hIoo hφle)
  have hval : φ 1 = ∑ k ∈ Finset.range N,
      ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2 := by
    rw [hφ]; simp
  rw [← hval]; exact hφ1

end GaloisForLFunctions.HTGeometry
