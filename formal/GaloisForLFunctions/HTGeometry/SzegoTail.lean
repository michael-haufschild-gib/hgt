import GaloisForLFunctions.HTGeometry.SzegoRadialMean

/-!
# The Taylor tail of `1/D`

The `n`-th Taylor partial sum `Sₙ` of `1/D` differs from `1/D` by the tail `∑_{k≥n} bₖ zᵏ`.  Its
circle mean is controlled by the coefficient tail `∑_{k≥n} ‖bₖ‖²`, which tends to `0` since
`1/D ∈ H²`.  This is the quantitative statement `Sₙ → 1/D in H²`, the last input to the Szegő upper
bound.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- A partial sum of a power series is analytic with its truncated series. -/
theorem hasFPowerSeriesOnBall_partialSum (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ)
    {R : NNReal} (hR : 0 < R) :
    HasFPowerSeriesOnBall (fun z => p.partialSum n z) (fun k => if k < n then p k else 0) 0 R where
  r_le := by
    rw [FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero _
      (Filter.eventually_atTop.mpr ⟨n, fun k hk => if_neg (not_lt.mpr hk)⟩)]
    exact le_top
  r_pos := by exact_mod_cast hR
  hasSum := by
    intro y _
    rw [zero_add]
    have hz : ∀ k, ((if k < n then p k else 0) fun _ => y)
        = if k < n then (p k fun _ => y) else 0 := fun k => by split <;> rfl
    simp only [hz]
    have hsum : (∑ k ∈ Finset.range n, if k < n then (p k fun _ => y) else 0)
        = p.partialSum n y := by
      rw [FormalMultilinearSeries.partialSum]
      exact Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero (fun k hk => if_neg (by simpa using hk))

/-- The Taylor partial sum of `1/D` is analytic on the disk. -/
theorem analyticOnNhd_partialSum_inv_szegoOuter (w : ℝ → ℝ) {R₀ : NNReal} (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun z => (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).partialSum n z)
      (Metric.ball 0 1) := by
  set p := cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀
  have hpoly : (fun z => p.partialSum n z) = fun z => ∑ k ∈ Finset.range n, p.coeff k * z ^ k := by
    funext z
    rw [FormalMultilinearSeries.partialSum]
    exact Finset.sum_congr rfl (fun k _ => by rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm])
  have hdiff : Differentiable ℂ (fun z => p.partialSum n z) := by rw [hpoly]; fun_prop
  exact hdiff.differentiableOn.analyticOnNhd Metric.isOpen_ball

/-- **The tail coefficients.**  `‖coeff(Sₙ − 1/D) k‖² = 0` for `k < n` and `‖bₖ‖²` for `k ≥ n`. -/
theorem normSq_coeff_partialSum_sub_inv {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1) (n : ℕ) (k : ℕ) :
    ‖(cauchyPowerSeries (fun z =>
          (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).partialSum n z
            - (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2
      = if k < n then 0 else ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2 := by
  set p := cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀ with hp
  set q : FormalMultilinearSeries ℂ ℂ ℂ := fun k => if k < n then p k else 0 with hq
  have hSn : HasFPowerSeriesOnBall (fun z => p.partialSum n z) q 0 R₀ :=
    hasFPowerSeriesOnBall_partialSum p n hR₀0
  have hinvD : HasFPowerSeriesOnBall (fun z => (szegoOuter w z)⁻¹) p 0 R₀ :=
    hasFPowerSeriesOnBall_inv_szegoOuter hlog hR₀0 hR₀1
  have hdiff := hSn.sub hinvD
  have hana : AnalyticOnNhd ℂ (fun z => p.partialSum n z - (szegoOuter w z)⁻¹) (Metric.ball 0 1) :=
    (analyticOnNhd_partialSum_inv_szegoOuter w n).sub (analyticOnNhd_inv_szegoOuter hlog)
  have hcps : cauchyPowerSeries (fun z => p.partialSum n z - (szegoOuter w z)⁻¹) 0 R₀ = q - p :=
    (hasFPowerSeriesOnBall_of_analyticOnNhd_ball hana hR₀0
      hR₀1).hasFPowerSeriesAt.eq_formalMultilinearSeries hdiff.hasFPowerSeriesAt
  rw [hcps]
  have hqcoeff : q.coeff k = if k < n then p.coeff k else 0 := by
    show (if k < n then p k else 0) (1 : Fin k → ℂ) = if k < n then (p k) 1 else 0
    split <;> simp
  have hcoeff : (q - p).coeff k = q.coeff k - p.coeff k := by
    show ((q - p) k) (1 : Fin k → ℂ) = (q k) 1 - (p k) 1
    exact sub_apply (q k) (p k) 1
  rw [hcoeff, hqcoeff]
  by_cases hk : k < n
  · rw [if_pos hk, if_pos hk, sub_self, norm_zero]; norm_num
  · rw [if_neg hk, if_neg hk, zero_sub, norm_neg]

/-- **The tail circle mean is bounded by the coefficient tail.**  For `r < 1`,
`circleMeanSq (Sₙ − 1/D) r ≤ ∑_{k≥n} ‖bₖ‖²`. -/
theorem circleMeanSq_partialSum_sub_inv_le {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hsum : Summable (fun k => ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2))
    (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleMeanSq (fun z =>
        (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).partialSum n z - (szegoOuter w z)⁻¹) r
      ≤ ∑' k, (if k < n then 0 else
          ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2) := by
  have hana : AnalyticOnNhd ℂ (fun z =>
      (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).partialSum n z - (szegoOuter w z)⁻¹)
      (Metric.ball 0 1) :=
    (analyticOnNhd_partialSum_inv_szegoOuter w n).sub (analyticOnNhd_inv_szegoOuter hlog)
  have hHS := hasSum_circleMeanSq hana hR₀0 hR₀1 hr0 hr1
  have htailsum : Summable (fun k => if k < n then (0:ℝ) else
      ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2) := by
    refine hsum.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    split
    · positivity
    · exact le_refl _
  rw [← hHS.tsum_eq]
  refine Summable.tsum_mono hHS.summable htailsum (fun k => ?_)
  rw [normSq_coeff_partialSum_sub_inv hlog hR₀0 hR₀1 n k]
  split
  · rw [zero_mul]
  · calc ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2 * r ^ (2 * k)
        ≤ ‖(cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1.le) (by positivity)
      _ = _ := mul_one _

/-- **The coefficient tail vanishes.**  For a summable nonnegative sequence, the tail
`∑_{k≥n} a k` (written with an indicator) tends to `0` as `n → ∞`. -/
theorem tendsto_tsum_tail_ite {a : ℕ → ℝ} (hsum : Summable a) :
    Tendsto (fun n => ∑' k, (if k < n then (0:ℝ) else a k)) atTop (𝓝 0) := by
  have hkey : ∀ n, (∑' k, (if k < n then (0:ℝ) else a k)) = ∑' k, a (k + n) := by
    intro n
    have hg : Function.Injective (fun k => k + n) := fun x y h => by simpa using h
    have hf : ∀ x ∉ Set.range (fun k => k + n), (if x < n then (0:ℝ) else a x) = 0 := by
      intro x hx
      rw [if_pos]
      by_contra hxn
      exact hx ⟨x - n, by simp only []; omega⟩
    have hcomp : ((fun k => if k < n then (0:ℝ) else a k) ∘ (fun k => k + n))
        = fun k => a (k + n) := by
      funext k
      simp only [Function.comp]
      rw [if_neg (by omega)]
    have hsummable : Summable (fun k => a (k + n)) := (summable_nat_add_iff n).mpr hsum
    have := (hg.hasSum_iff hf).mp (hcomp ▸ hsummable.hasSum)
    rw [this.tsum_eq, hcomp]
  simp only [hkey]
  exact tendsto_sum_nat_add a

end GaloisForLFunctions.HTGeometry
