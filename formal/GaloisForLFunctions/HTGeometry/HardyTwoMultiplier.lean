import GaloisForLFunctions.HTGeometry.SzegoRadialMean

/-!
# Bounded analytic multipliers of the coefficient Hardy space

A function analytic on the unit disk with square-summable Taylor coefficients is an `H²` function,
and multiplying it by a bounded analytic function multiplies the coefficient sum by at most the
supremum of the multiplier: Gutzmer's identity turns the pointwise bound on each circle into a bound
on the coefficient sums, and letting the radius tend to one keeps it.

This is the Szegő-outer multiplier bound of `SzegoRadialMean.lean` with the outer function replaced
by an arbitrary bounded analytic factor, together with the linearity and truncation of Taylor
coefficients needed to approximate.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Interior multiplier bound.**  A pointwise bound on the multiplier contracts every circle
mean. -/
theorem circleMeanSq_mul_le {g O : ℂ → ℂ} {C : ℝ} (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1))
    (hO : AnalyticOnNhd ℂ O (Metric.ball 0 1))
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖O z‖ ^ 2 ≤ C) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleMeanSq (fun z => g z * O z) r ≤ C * circleMeanSq g r := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hin : ∀ θ, circleMap 0 r θ ∈ Metric.ball (0 : ℂ) 1 := by
    intro θ
    rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
    exact hr1
  have hgc := continuous_normSq_circleMap hg hr0 hr1
  have hgcont : Continuous (fun θ : ℝ => g (circleMap 0 r θ)) :=
    hg.continuousOn.comp_continuous (continuous_circleMap 0 r) hin
  have hOcont : Continuous (fun θ : ℝ => O (circleMap 0 r θ)) :=
    hO.continuousOn.comp_continuous (continuous_circleMap 0 r) hin
  have hIntL : Continuous (fun θ : ℝ => ‖g (circleMap 0 r θ) * O (circleMap 0 r θ)‖ ^ 2) :=
    (hgcont.mul hOcont).norm.pow 2
  have hle : (∫ θ in (0 : ℝ)..(2 * π), ‖g (circleMap 0 r θ) * O (circleMap 0 r θ)‖ ^ 2)
      ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖g (circleMap 0 r θ)‖ ^ 2 * C := by
    apply intervalIntegral.integral_mono_on hπ.le (hIntL.intervalIntegrable _ _)
      ((hgc.mul continuous_const).intervalIntegrable _ _)
    intro θ _
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (hC _ (hin θ)) (by positivity)
  calc circleMeanSq (fun z => g z * O z) r
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖g (circleMap 0 r θ) * O (circleMap 0 r θ)‖ ^ 2 := rfl
    _ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖g (circleMap 0 r θ)‖ ^ 2 * C :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C * circleMeanSq g r := by
        rw [intervalIntegral.integral_mul_const, circleMeanSq]
        ring

/-- **The `H²` multiplier bound on partial sums.**  A bounded analytic factor multiplies every
partial coefficient sum by at most its bound. -/
theorem sum_range_normSq_coeff_mul_le {g O : ℂ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1)) (hO : AnalyticOnNhd ℂ O (Metric.ball 0 1))
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖O z‖ ^ 2 ≤ C)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hgsum : Summable fun k => ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2) (N : ℕ) :
    ∑ k ∈ Finset.range N, ‖(cauchyPowerSeries (fun z => g z * O z) 0 R₀).coeff k‖ ^ 2
      ≤ C * ∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 := by
  have hgO : AnalyticOnNhd ℂ (fun z => g z * O z) (Metric.ball 0 1) := hg.mul hO
  set M : ℝ := C * ∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 with hM
  have hkey : ∀ (N : ℕ) (r : ℝ), 0 ≤ r → r < 1 →
      ∑ k ∈ Finset.range N,
          ‖(cauchyPowerSeries (fun z => g z * O z) 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k) ≤ M := by
    intro N r hr0 hr1
    have h1 := sum_range_le_circleMeanSq hgO hR₀0 hR₀1 hr0 hr1 N
    have h2 := circleMeanSq_mul_le hg hO hC hr0 hr1
    have h3 : circleMeanSq g r ≤ ∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 := by
      rw [← (hasSum_circleMeanSq hg hR₀0 hR₀1 hr0 hr1).tsum_eq]
      refine Summable.tsum_mono (hasSum_circleMeanSq hg hR₀0 hR₀1 hr0 hr1).summable hgsum
        fun k => ?_
      calc ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)
          ≤ ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1.le) (by positivity)
        _ = ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 := mul_one _
    calc ∑ k ∈ Finset.range N,
            ‖(cauchyPowerSeries (fun z => g z * O z) 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)
        ≤ circleMeanSq (fun z => g z * O z) r := h1
      _ ≤ C * circleMeanSq g r := h2
      _ ≤ M := mul_le_mul_of_nonneg_left h3 hC0
  have hstep : ∀ N, ∑ k ∈ Finset.range N,
      ‖(cauchyPowerSeries (fun z => g z * O z) 0 R₀).coeff k‖ ^ 2 ≤ M := by
    intro N
    set φ : ℝ → ℝ := fun r => ∑ k ∈ Finset.range N,
        ‖(cauchyPowerSeries (fun z => g z * O z) 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k) with hφ
    have hφcont : Continuous φ := by
      rw [hφ]
      exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_pow (2 * k))
    have hIoo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
      rw [← Set.Ioi_inter_Iio]
      exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
    have hlim : Tendsto φ (𝓝[<] (1 : ℝ)) (𝓝 (φ 1)) := (hφcont.tendsto 1).mono_left nhdsWithin_le_nhds
    have hφ1 : φ 1 ≤ M := le_of_tendsto hlim
      (Filter.eventually_of_mem hIoo fun r hr => hkey N r (le_of_lt hr.1) hr.2)
    have hval : φ 1 = ∑ k ∈ Finset.range N,
        ‖(cauchyPowerSeries (fun z => g z * O z) 0 R₀).coeff k‖ ^ 2 := by
      rw [hφ]
      simp
    rwa [hval] at hφ1
  exact hstep N

/-- **The `H²` multiplier inequality.**  A bounded analytic factor multiplies the coefficient sum by
at most its bound. -/
theorem tsum_normSq_coeff_mul_le {g O : ℂ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1)) (hO : AnalyticOnNhd ℂ O (Metric.ball 0 1))
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖O z‖ ^ 2 ≤ C)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hgsum : Summable fun k => ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2) :
    ∑' k, ‖(cauchyPowerSeries (fun z => g z * O z) 0 R₀).coeff k‖ ^ 2
      ≤ C * ∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 :=
  Real.tsum_le_of_sum_range_le (fun k => by positivity)
    (sum_range_normSq_coeff_mul_le hC0 hg hO hC hR₀0 hR₀1 hgsum)

/-- The product of an `H²` function with a bounded analytic factor is again `H²`. -/
theorem summable_normSq_coeff_mul {g O : ℂ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1)) (hO : AnalyticOnNhd ℂ O (Metric.ball 0 1))
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖O z‖ ^ 2 ≤ C)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hgsum : Summable fun k => ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2) :
    Summable fun k => ‖(cauchyPowerSeries (fun z => g z * O z) 0 R₀).coeff k‖ ^ 2 :=
  summable_of_sum_range_le (fun k => by positivity)
    (sum_range_normSq_coeff_mul_le hC0 hg hO hC hR₀0 hR₀1 hgsum)

/-- Taylor coefficients are additive. -/
theorem cauchyPowerSeries_sub {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1)) {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1) :
    cauchyPowerSeries (fun z => f z - g z) 0 R
      = cauchyPowerSeries f 0 R - cauchyPowerSeries g 0 R := by
  have h1 : HasFPowerSeriesOnBall (fun z => f z - g z)
      (cauchyPowerSeries (fun z => f z - g z) 0 R) 0 R :=
    hasFPowerSeriesOnBall_of_analyticOnNhd_ball (hf.sub hg) hR0 hR1
  have h2 : HasFPowerSeriesOnBall (fun z => f z - g z)
      (cauchyPowerSeries f 0 R - cauchyPowerSeries g 0 R) 0 R :=
    (hasFPowerSeriesOnBall_of_analyticOnNhd_ball hf hR0 hR1).sub
      (hasFPowerSeriesOnBall_of_analyticOnNhd_ball hg hR0 hR1)
  exact h1.hasFPowerSeriesAt.eq_formalMultilinearSeries h2.hasFPowerSeriesAt

/-- The truncation of a formal power series after `N` terms. -/
def truncSeries_hardyTwoMultiplier (P : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n => if n < N then P n else 0

theorem truncSeries_radius (P : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) :
    (truncSeries_hardyTwoMultiplier P N).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero _ ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [truncSeries_hardyTwoMultiplier, if_neg (Nat.not_lt.mpr hn)]

theorem coeff_truncSeries (P : FormalMultilinearSeries ℂ ℂ ℂ) (N k : ℕ) :
    (truncSeries_hardyTwoMultiplier P N).coeff k = if k < N then P.coeff k else 0 := by
  rw [FormalMultilinearSeries.coeff, truncSeries_hardyTwoMultiplier]
  by_cases h : k < N
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- The partial sums of a power series are its own truncations. -/
theorem hasFPowerSeriesOnBall_partialSum_truncSeries (P : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) :
    HasFPowerSeriesOnBall (fun z => P.partialSum N z) (truncSeries_hardyTwoMultiplier P N) 0 ⊤ where
  r_le := by rw [truncSeries_radius]
  r_pos := by simp
  hasSum := by
    intro y _
    have hzero : ∀ n ∉ Finset.range N, (truncSeries_hardyTwoMultiplier P N) n (fun _ => y) = 0 := by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [truncSeries_hardyTwoMultiplier, if_neg hn]
      rfl
    have hval : P.partialSum N (0 + y)
        = ∑ n ∈ Finset.range N, (truncSeries_hardyTwoMultiplier P N) n (fun _ => y) := by
      rw [zero_add, FormalMultilinearSeries.partialSum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [truncSeries_hardyTwoMultiplier, if_pos (Finset.mem_range.mp hn)]
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero hzero

theorem cauchyPowerSeries_partialSum {f : ℂ → ℂ} {R : NNReal} (N : ℕ) (hR0 : 0 < R)
    (hR1 : (R : ℝ) < 1) :
    cauchyPowerSeries (fun z => (cauchyPowerSeries f 0 R).partialSum N z) 0 R
      = truncSeries_hardyTwoMultiplier (cauchyPowerSeries f 0 R) N := by
  have hana : AnalyticOnNhd ℂ (fun z => (cauchyPowerSeries f 0 R).partialSum N z)
      (Metric.ball 0 1) := by
    intro z _
    exact (hasFPowerSeriesOnBall_partialSum_truncSeries (cauchyPowerSeries f 0 R) N).analyticAt_of_mem
      (by simp)
  have h1 := hasFPowerSeriesOnBall_of_analyticOnNhd_ball hana hR0 hR1
  exact h1.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesOnBall_partialSum_truncSeries (cauchyPowerSeries f 0 R) N).hasFPowerSeriesAt

end

end GaloisForLFunctions.HTGeometry
