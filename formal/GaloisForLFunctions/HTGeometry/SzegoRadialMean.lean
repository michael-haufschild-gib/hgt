import GaloisForLFunctions.HTGeometry.GutzmerIdentity
import GaloisForLFunctions.HTGeometry.SzegoHInfty
import GaloisForLFunctions.HTGeometry.SzegoOuterAnalytic

/-!
# Radial circle means and the `H^∞` multiplier inequality

For a disk-analytic function `f`, `circleMeanSq f r = (2π)⁻¹∫₀²π ‖f(re^{iθ})‖²` is its radial circle
mean; Gutzmer expresses it as the coefficient sum `∑ₖ ‖bₖ‖² r^{2k}`.  Multiplying by the outer
function `D` (bounded, `‖D‖²≤C`) contracts the mean by at most `C`.  Pushing this through the
`r → 1`, `N → ∞` limits gives the `H²` multiplier bound `‖gD‖²_{H²} ≤ C‖g‖²_{H²}`, the pointwise
disk estimate promoted to the coefficient sums.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- The radial circle mean of `‖f‖²` at radius `r`. -/
noncomputable def circleMeanSq (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2

/-- **Gutzmer with a fixed reference radius.**  For `f` analytic on the disk and `r < 1`, the circle
mean is the coefficient sum with respect to a *fixed* reference series `cauchyPowerSeries f 0 R₀`. -/
theorem hasSum_circleMeanSq {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k => ‖(cauchyPowerSeries f 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)) (circleMeanSq f r) := by
  obtain ⟨s, hrs, hs1⟩ := exists_between hr1
  have hs0 : (0:ℝ) ≤ s := le_of_lt (lt_of_le_of_lt hr0 hrs)
  have hSpos : 0 < s.toNNReal := Real.toNNReal_pos.mpr (lt_of_le_of_lt hr0 hrs)
  have hS1 : (s.toNNReal : ℝ) < 1 := by rw [Real.coe_toNNReal s hs0]; exact hs1
  have hrS : r < (s.toNNReal : ℝ) := by rw [Real.coe_toNNReal s hs0]; exact hrs
  have h := hasSum_gutzmer hf hSpos hS1 hr0 hrS
  rw [cauchyPowerSeries_eq_of_analyticOnNhd_ball hf hSpos hS1 hR₀0 hR₀1] at h
  exact h

/-- Every partial coefficient sum is bounded by the circle mean. -/
theorem sum_range_le_circleMeanSq {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, ‖(cauchyPowerSeries f 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)
      ≤ circleMeanSq f r :=
  sum_le_hasSum _ (fun i _ => by positivity) (hasSum_circleMeanSq hf hR₀0 hR₀1 hr0 hr1)

/-- Continuity of the disk-analytic integrand on a radius-`r` circle. -/
theorem continuous_normSq_circleMap {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun θ : ℝ => ‖g (circleMap 0 r θ)‖ ^ 2) := by
  have hin : ∀ θ, circleMap 0 r θ ∈ Metric.ball (0:ℂ) 1 := by
    intro θ
    rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
    exact hr1
  exact ((hg.continuousOn.comp_continuous (continuous_circleMap 0 r) hin).norm.pow 2)

/-- **Interior multiplier bound at radius `r`.**  For a positive weight bounded above by `C`,
multiplying by the outer function contracts the circle mean by at most `C`. -/
theorem circleMeanSq_mul_szegoOuter_le {g : ℂ → ℂ} {w : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1))
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwpos : ∀ θ, 0 < w θ) (hwC : ∀ θ, w θ ≤ C) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleMeanSq (fun z => g z * szegoOuter w z) r ≤ C * circleMeanSq g r := by
  have hπ : (0:ℝ) < 2 * π := by positivity
  have hgc := continuous_normSq_circleMap hg hr0 hr1
  have hle : (∫ θ in (0:ℝ)..(2 * π), ‖g (circleMap 0 r θ) * szegoOuter w (circleMap 0 r θ)‖ ^ 2)
      ≤ ∫ θ in (0:ℝ)..(2 * π), ‖g (circleMap 0 r θ)‖ ^ 2 * C := by
    have hIntL : Continuous
        (fun θ : ℝ => ‖g (circleMap 0 r θ) * szegoOuter w (circleMap 0 r θ)‖ ^ 2) := by
      have hDc : Continuous (fun θ : ℝ => szegoOuter w (circleMap 0 r θ)) := by
        have hin : ∀ θ, circleMap 0 r θ ∈ Metric.ball (0:ℂ) 1 := by
          intro θ
          rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
          exact hr1
        exact (analyticOnNhd_szegoOuter hlog).continuousOn.comp_continuous
          (continuous_circleMap 0 r) hin
      have hgcont : Continuous (fun θ : ℝ => g (circleMap 0 r θ)) := by
        have hin : ∀ θ, circleMap 0 r θ ∈ Metric.ball (0:ℂ) 1 := by
          intro θ
          rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
          exact hr1
        exact hg.continuousOn.comp_continuous (continuous_circleMap 0 r) hin
      exact ((hgcont.mul hDc).norm.pow 2)
    apply intervalIntegral.integral_mono_on hπ.le (hIntL.intervalIntegrable _ _)
      ((hgc.mul continuous_const).intervalIntegrable _ _)
    intro θ _
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (normSq_szegoOuter_le hC hlog hper hlogφ hwpos hwC hr0 hr1 θ) (by positivity)
  calc circleMeanSq (fun z => g z * szegoOuter w z) r
      = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
          ‖g (circleMap 0 r θ) * szegoOuter w (circleMap 0 r θ)‖ ^ 2 := rfl
    _ ≤ (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖g (circleMap 0 r θ)‖ ^ 2 * C :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C * circleMeanSq g r := by
        rw [intervalIntegral.integral_mul_const, circleMeanSq]; ring

/-- **The `H²` multiplier inequality.**  For a positive weight bounded above by `C`, the coefficient
sum of `g · D` is `≤ C` times that of `g`.  This promotes the pointwise disk bound `‖D‖²≤C` through
the `r → 1` and `N → ∞` limits, giving `‖gD‖²_{H²} ≤ C‖g‖²_{H²}`. -/
theorem tsum_normSq_coeff_mul_szegoOuter_le {g : ℂ → ℂ} {w : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1))
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwpos : ∀ θ, 0 < w θ) (hwC : ∀ θ, w θ ≤ C)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hgsum : Summable (fun k => ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2)) :
    ∑' k, ‖(cauchyPowerSeries (fun z => g z * szegoOuter w z) 0 R₀).coeff k‖ ^ 2
      ≤ C * ∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 := by
  have hgD : AnalyticOnNhd ℂ (fun z => g z * szegoOuter w z) (Metric.ball 0 1) :=
    hg.mul (analyticOnNhd_szegoOuter hlog)
  set M : ℝ := C * ∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 with hM
  have hkey : ∀ (N : ℕ) (r : ℝ), 0 ≤ r → r < 1 →
      ∑ k ∈ Finset.range N,
          ‖(cauchyPowerSeries (fun z => g z * szegoOuter w z) 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)
        ≤ M := by
    intro N r hr0 hr1
    have h1 := sum_range_le_circleMeanSq hgD hR₀0 hR₀1 hr0 hr1 N
    have h2 := circleMeanSq_mul_szegoOuter_le hC hg hlog hper hlogφ hwpos hwC hr0 hr1
    have h3 : circleMeanSq g r ≤ ∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 := by
      rw [← (hasSum_circleMeanSq hg hR₀0 hR₀1 hr0 hr1).tsum_eq]
      refine Summable.tsum_mono (hasSum_circleMeanSq hg hR₀0 hR₀1 hr0 hr1).summable hgsum (fun k => ?_)
      calc ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)
          ≤ ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1.le) (by positivity)
        _ = ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 := mul_one _
    calc ∑ k ∈ Finset.range N,
            ‖(cauchyPowerSeries (fun z => g z * szegoOuter w z) 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)
        ≤ circleMeanSq (fun z => g z * szegoOuter w z) r := h1
      _ ≤ C * circleMeanSq g r := h2
      _ ≤ M := mul_le_mul_of_nonneg_left h3 hC.le
  have hstep : ∀ N, ∑ k ∈ Finset.range N,
      ‖(cauchyPowerSeries (fun z => g z * szegoOuter w z) 0 R₀).coeff k‖ ^ 2 ≤ M := by
    intro N
    set φ : ℝ → ℝ := fun r => ∑ k ∈ Finset.range N,
        ‖(cauchyPowerSeries (fun z => g z * szegoOuter w z) 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)
      with hφ
    have hφcont : Continuous φ := by
      rw [hφ]
      exact continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_pow (2 * k)))
    have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := by
      rw [← Set.Ioi_inter_Iio]
      exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
    have hlim : Tendsto φ (𝓝[<] (1:ℝ)) (𝓝 (φ 1)) := (hφcont.tendsto 1).mono_left nhdsWithin_le_nhds
    have hφ1 : φ 1 ≤ M := le_of_tendsto hlim
      (Filter.eventually_of_mem hIoo (fun r hr => hkey N r (le_of_lt hr.1) hr.2))
    have hval : φ 1 = ∑ k ∈ Finset.range N,
        ‖(cauchyPowerSeries (fun z => g z * szegoOuter w z) 0 R₀).coeff k‖ ^ 2 := by
      rw [hφ]; simp
    rwa [hval] at hφ1
  exact Real.tsum_le_of_sum_range_le (fun k => by positivity) hstep

/-- **Orthogonal decomposition of the circle mean.**  If `G` is disk-analytic with `G(0) = 0`, then
`circleMeanSq (1 + G) r = 1 + circleMeanSq G r`.  The cross term vanishes by the mean-value property
`(2π)⁻¹∫₀²π G(re^{iφ}) = G(0) = 0`. -/
theorem circleMeanSq_one_add {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G (Metric.ball 0 1))
    (hG0 : G 0 = 0) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleMeanSq (fun z => 1 + G z) r = 1 + circleMeanSq G r := by
  have hin : ∀ θ, circleMap 0 r θ ∈ Metric.ball (0:ℂ) 1 := by
    intro θ
    rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]; exact hr1
  have hGc : Continuous (fun θ : ℝ => G (circleMap 0 r θ)) :=
    hG.continuousOn.comp_continuous (continuous_circleMap 0 r) hin
  have habs : |r| = r := abs_of_nonneg hr0
  have hdcc : DiffContOnCl ℂ G (Metric.ball 0 |r|) := by
    rw [habs]
    exact ⟨hG.differentiableOn.mono (Metric.ball_subset_ball hr1.le),
      hG.continuousOn.mono (subset_trans Metric.closure_ball_subset_closedBall
        (Metric.closedBall_subset_ball hr1))⟩
  have hmv : Real.circleAverage G 0 r = G 0 := hdcc.circleAverage
  rw [Real.circleAverage_def, hG0] at hmv
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hintG : (∫ θ in (0:ℝ)..(2 * π), G (circleMap 0 r θ)) = 0 := by
    rcases smul_eq_zero.mp hmv with h | h
    · exact absurd (inv_eq_zero.mp h) h2π
    · exact h
  have hcomm : (∫ φ in (0:ℝ)..(2 * π), (G (circleMap 0 r φ)).re)
      = (∫ φ in (0:ℝ)..(2 * π), G (circleMap 0 r φ)).re := by
    rw [← Complex.reCLM_apply,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hGc.intervalIntegrable _ _)]; rfl
  have hmid : (∫ θ in (0:ℝ)..(2 * π), (G (circleMap 0 r θ)).re) = 0 := by
    rw [hcomm, hintG, Complex.zero_re]
  have hpt : ∀ θ, ‖1 + G (circleMap 0 r θ)‖ ^ 2
      = 1 + 2 * (G (circleMap 0 r θ)).re + ‖G (circleMap 0 r θ)‖ ^ 2 := fun θ => by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp [Complex.normSq_one]; ring
  have hi1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 (2 * π) := intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun θ : ℝ => 2 * (G (circleMap 0 r θ)).re) volume 0 (2 * π) :=
    (continuous_const.mul (Complex.continuous_re.comp hGc)).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun θ : ℝ => ‖G (circleMap 0 r θ)‖ ^ 2) volume 0 (2 * π) :=
    (hGc.norm.pow 2).intervalIntegrable _ _
  simp only [circleMeanSq]
  rw [intervalIntegral.integral_congr (g := fun θ =>
        1 + 2 * (G (circleMap 0 r θ)).re + ‖G (circleMap 0 r θ)‖ ^ 2) (fun θ _ => hpt θ),
    intervalIntegral.integral_add (hi1.add hi2) hi3,
    intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hmid,
    smul_eq_mul, mul_one]
  rw [mul_add, sub_zero, mul_zero, add_zero, inv_mul_cancel₀ h2π]

end GaloisForLFunctions.HTGeometry
