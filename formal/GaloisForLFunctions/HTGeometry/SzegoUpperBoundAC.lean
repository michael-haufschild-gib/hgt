import GaloisForLFunctions.HTGeometry.SzegoBoundaryLimit
import GaloisForLFunctions.HTGeometry.SzegoTail

/-!
# The Szegő boundary integral for absolutely continuous bounded weights

Assembling the radial-mean machinery: for a weight `0 < c ≤ w ≤ C`, the boundary Szegő integral of
the `n`-th normalized Taylor sum of `1/D` is `≤ 1 + C·(tail of ‖bₖ‖²)`.  As `n → ∞` the tail
vanishes, so the integral tends to `1`; scaled by `|D(0)|² = GM` this is the Szegő upper bound for
the absolutely continuous part.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- **The interior Szegő bound.**  `(2π)⁻¹∫₀²π ‖Sₙ(e^{iφ})‖² w(φ) ≤ 1 + C·(∑_{k≥n} ‖bₖ‖²)`. -/
theorem boundary_integral_partialSum_le {w : ℝ → ℝ} {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlogLI : LocallyIntegrable (fun θ => Real.log (w θ)) volume)
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwc : ∀ θ, c ≤ w θ) (hwC : ∀ θ, w θ ≤ C)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hsum : Summable (fun k => ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2))
    {n : ℕ} (hn : 1 ≤ n) :
    (2 * π)⁻¹ * ∫ φ in (0:ℝ)..(2 * π),
        ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).partialSum n (circleMap 0 1 φ)‖ ^ 2
          * w φ
      ≤ 1 + C * ∑' k, (if k < n then 0 else
          ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2) := by
  set p := cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀ with hp
  have hwpos : ∀ θ, 0 < w θ := fun θ => lt_of_lt_of_le hc (hwc θ)
  have hDne : ∀ z, szegoOuter w z ≠ 0 := szegoOuter_ne_zero w
  -- `Sₙ` is a polynomial, hence continuous and disk-analytic
  have hpoly : (fun z => p.partialSum n z) = fun z => ∑ k ∈ Finset.range n, p.coeff k * z ^ k := by
    funext z
    rw [FormalMultilinearSeries.partialSum]
    exact Finset.sum_congr rfl (fun k _ => by rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm])
  have hSncont : Continuous (fun z => p.partialSum n z) := by rw [hpoly]; fun_prop
  have hSnana : AnalyticOnNhd ℂ (fun z => p.partialSum n z) (Metric.ball 0 1) :=
    analyticOnNhd_partialSum_inv_szegoOuter w n
  -- boundary limit = the target integral
  have hDC := tendsto_circleMeanSq_mul_szegoOuter hSncont hC hlogLI hlog hper hlogφ hwpos hwC
  -- `Sₙ(0) = p.coeff 0 = 1/D(0)`
  have hSn0 : p.partialSum n 0 = (szegoOuter w 0)⁻¹ := by
    rw [FormalMultilinearSeries.partialSum, Finset.sum_eq_single 0]
    · rw [p.apply_eq_pow_smul_coeff, pow_zero, one_smul]
      exact (hasFPowerSeriesOnBall_inv_szegoOuter hlog hR₀0 hR₀1).coeff_zero 1
    · intro k _ hk0
      rw [p.apply_eq_pow_smul_coeff, zero_pow hk0, zero_smul]
    · intro h
      exact absurd (Finset.mem_range.mpr hn) h
  -- per-radius bound
  have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
  refine le_of_tendsto hDC (Filter.eventually_of_mem hIoo (fun r hr => ?_))
  obtain ⟨hr0, hr1⟩ := hr
  -- `G_n := Sₙ·D − 1`, analytic with `G_n(0) = 0`
  have hG0 : (fun z => p.partialSum n z * szegoOuter w z - 1) (0 : ℂ) = 0 := by
    simp only [hSn0]
    rw [inv_mul_cancel₀ (hDne 0), sub_self]
  have hGana : AnalyticOnNhd ℂ (fun z => p.partialSum n z * szegoOuter w z - 1) (Metric.ball 0 1) :=
    (hSnana.mul (analyticOnNhd_szegoOuter hlog)).sub analyticOnNhd_const
  -- `Sₙ·D = 1 + G_n`
  have heq1 : (fun z => p.partialSum n z * szegoOuter w z)
      = fun z => 1 + (p.partialSum n z * szegoOuter w z - 1) := by funext z; ring
  -- `G_n = (Sₙ − 1/D)·D`
  have heq2 : (fun z => p.partialSum n z * szegoOuter w z - 1)
      = fun z => (p.partialSum n z - (szegoOuter w z)⁻¹) * szegoOuter w z := by
    funext z
    rw [sub_mul, inv_mul_cancel₀ (hDne z)]
  calc circleMeanSq (fun z => p.partialSum n z * szegoOuter w z) r
      = circleMeanSq (fun z => 1 + (p.partialSum n z * szegoOuter w z - 1)) r := by rw [heq1]
    _ = 1 + circleMeanSq (fun z => p.partialSum n z * szegoOuter w z - 1) r :=
        circleMeanSq_one_add hGana hG0 hr0.le hr1
    _ = 1 + circleMeanSq
          (fun z => (p.partialSum n z - (szegoOuter w z)⁻¹) * szegoOuter w z) r := by rw [heq2]
    _ ≤ 1 + C * circleMeanSq (fun z => p.partialSum n z - (szegoOuter w z)⁻¹) r := by
        have hHana : AnalyticOnNhd ℂ (fun z => p.partialSum n z - (szegoOuter w z)⁻¹)
            (Metric.ball 0 1) := hSnana.sub (analyticOnNhd_inv_szegoOuter hlog)
        have := circleMeanSq_mul_szegoOuter_le hC hHana hlog hper hlogφ hwpos hwC hr0.le hr1
        linarith
    _ ≤ 1 + C * ∑' k, (if k < n then 0 else ‖p.coeff k‖ ^ 2) := by
        have htail := circleMeanSq_partialSum_sub_inv_le hlog hR₀0 hR₀1 hsum n hr0.le hr1
        rw [← hp] at htail
        have h := mul_le_mul_of_nonneg_left htail hC.le
        linarith

/-- **The interior Szegő bound tends to `1`.**  Since the coefficient tail vanishes, for every
`δ > 0` there is a degree `n ≥ 1` with `(2π)⁻¹∫₀²π ‖Sₙ(e^{iφ})‖² w(φ) ≤ 1 + δ`. -/
theorem exists_boundary_integral_partialSum_le {w : ℝ → ℝ} {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlogLI : LocallyIntegrable (fun θ => Real.log (w θ)) volume)
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwc : ∀ θ, c ≤ w θ) (hwC : ∀ θ, w θ ≤ C)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hsum : Summable (fun k => ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 2 ≤ n ∧
      (2 * π)⁻¹ * ∫ φ in (0:ℝ)..(2 * π),
        ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).partialSum n (circleMap 0 1 φ)‖ ^ 2
          * w φ ≤ 1 + δ := by
  set p := cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀ with hp
  -- the tail multiplied by `C` tends to `0`
  have htail0 : Tendsto (fun n => C * ∑' k, (if k < n then (0:ℝ) else ‖p.coeff k‖ ^ 2))
      atTop (𝓝 0) := by
    have := (tendsto_tsum_tail_ite hsum).const_mul C
    simpa using this
  -- eventually the tail term is `< δ` and `n ≥ 2`
  have hev : ∀ᶠ n in atTop, C * ∑' k, (if k < n then (0:ℝ) else ‖p.coeff k‖ ^ 2) < δ :=
    htail0.eventually_lt_const hδ
  obtain ⟨n, hnδ, hn2⟩ := ((hev.and (eventually_ge_atTop 2))).exists
  refine ⟨n, hn2, ?_⟩
  have hmaster := boundary_integral_partialSum_le hc hC hlogLI hlog hper hlogφ hwc hwC
    hR₀0 hR₀1 hsum (by omega : 1 ≤ n)
  rw [← hp] at hmaster
  linarith [hmaster, hnδ.le]

end GaloisForLFunctions.HTGeometry
