import GaloisForLFunctions.HTGeometry.GutzmerIdentity
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# Gutzmer's identity for an entire power series

For a coefficient sequence whose series converges everywhere, the circle mean of `‖f‖²` at radius `r`
is the coefficient sum `∑ₖ ‖aₖ‖² r^{2k}`.  The disk version already in the corpus is stated through
the Cauchy power series of a function analytic on the unit ball; here the series is given first, so
the only work is to feed the two hypotheses of the general passage-to-the-limit lemma — that `r` is
inside the radius of convergence, and that the partial sums converge uniformly on the circle.

The consequence used downstream is Bessel's inequality: the coefficient sum is at most the square of
any bound for `‖f‖` on the circle.  It is the lower bound on the maximum modulus that no estimate of
the individual coefficients can supply — it says the terms cannot all cancel at once.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The partial sums of an entire series converge uniformly on every circle. -/
theorem tendstoUniformlyOn_partialSum_coeffFun_circleMap (ha : EntireCoeffs a) {r : ℝ}
    (hr0 : 0 ≤ r) :
    TendstoUniformlyOn
      (fun n θ => (FormalMultilinearSeries.ofScalars ℂ a).partialSum n (circleMap 0 r θ))
      (fun θ => coeffFun a (circleMap 0 r θ)) atTop Set.univ := by
  have hrad : (FormalMultilinearSeries.ofScalars ℂ a).radius = ⊤ := ofScalars_radius_eq_top ha
  have hpos : 0 < (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    rw [hrad]; exact ENNReal.zero_lt_top
  have hball : HasFPowerSeriesOnBall (coeffFun a) (FormalMultilinearSeries.ofScalars ℂ a) 0
      (FormalMultilinearSeries.ofScalars ℂ a).radius :=
    (FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall hpos
  set r' : NNReal := ⟨r + 1, by linarith⟩ with hr'
  have hr'lt : ((r' : ℝ≥0∞)) < (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    rw [hrad]; exact ENNReal.coe_lt_top
  have hunif := hball.tendstoUniformlyOn hr'lt
  have hcomp := hunif.comp (circleMap 0 r)
  have hset : (circleMap 0 r) ⁻¹' (Metric.ball 0 (r' : ℝ)) = Set.univ := by
    ext θ
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hr0, Set.mem_univ, iff_true]
    show r < r + 1
    linarith
  rw [hset] at hcomp
  refine hcomp.congr_right ?_
  intro θ _
  simp [Function.comp, zero_add]

/-- **Gutzmer's identity for an entire series.**  The circle mean of `‖f‖²` at radius `r` is the
coefficient sum `∑ₖ ‖aₖ‖² r^{2k}`. -/
theorem hasSum_gutzmer_coeffFun (ha : EntireCoeffs a) {r : ℝ} (hr0 : 0 ≤ r) :
    HasSum (fun k => ‖a k‖ ^ 2 * r ^ (2 * k))
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖coeffFun a (circleMap 0 r θ)‖ ^ 2) := by
  have hrad : (FormalMultilinearSeries.ofScalars ℂ a).radius = ⊤ := ofScalars_radius_eq_top ha
  have hlt : (↑(r.toNNReal) : ℝ≥0∞) < (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    rw [hrad]; exact ENNReal.coe_lt_top
  have hcoeff : ∀ k : ℕ, (FormalMultilinearSeries.ofScalars ℂ a).coeff k = a k := by
    intro k
    simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]
  have htend := tendsto_integral_normSq_partialSum_of_radius_of_uniform hr0 hlt
    (tendstoUniformlyOn_partialSum_coeffFun_circleMap ha hr0)
  have htend' := htend.const_mul ((2 * π)⁻¹)
  rw [funext fun N => circleAverage_normSq_partialSum
    (FormalMultilinearSeries.ofScalars ℂ a) r N] at htend'
  have htend'' : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖a k‖ ^ 2 * r ^ (2 * k)) atTop
      (𝓝 ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖coeffFun a (circleMap 0 r θ)‖ ^ 2)) := by
    refine htend'.congr fun N => ?_
    exact Finset.sum_congr rfl fun k _ => by rw [hcoeff k]
  have hmono : Monotone (fun N => ∑ k ∈ Finset.range N, ‖a k‖ ^ 2 * r ^ (2 * k)) := by
    refine monotone_nat_of_le_succ fun n => ?_
    rw [Finset.sum_range_succ]
    have : (0 : ℝ) ≤ ‖a n‖ ^ 2 * r ^ (2 * n) := by positivity
    linarith
  have hsummable : Summable fun k => ‖a k‖ ^ 2 * r ^ (2 * k) :=
    summable_of_sum_range_le (fun n => by positivity) fun n => hmono.ge_of_tendsto htend'' n
  have hts := hsummable.hasSum
  rwa [tendsto_nhds_unique hsummable.hasSum.tendsto_sum_nat htend''] at hts

/-- **Bessel's inequality on a circle.**  The coefficient sum is at most the square of any bound for
`‖f‖` on the circle of radius `r`. -/
theorem tsum_normSq_coeff_le_of_bound (ha : EntireCoeffs a) {r : ℝ} (hr0 : 0 ≤ r) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 r θ)‖ ≤ M) :
    ∑' k : ℕ, ‖a k‖ ^ 2 * r ^ (2 * k) ≤ M ^ 2 := by
  have hg := hasSum_gutzmer_coeffFun ha hr0
  rw [hg.tsum_eq]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hcont : Continuous fun θ : ℝ => ‖coeffFun a (circleMap 0 r θ)‖ ^ 2 := by
    have hdiff : Continuous (coeffFun a) := (differentiable_coeffFun ha).continuous
    exact ((hdiff.comp (continuous_circleMap 0 r)).norm).pow 2
  have hint : (∫ θ in (0:ℝ)..(2 * π), ‖coeffFun a (circleMap 0 r θ)‖ ^ 2)
      ≤ ∫ _θ in (0:ℝ)..(2 * π), M ^ 2 := by
    refine intervalIntegral.integral_mono_on hpi.le (hcont.intervalIntegrable 0 (2 * π))
      intervalIntegrable_const fun θ _ => ?_
    have := hM θ
    nlinarith [norm_nonneg (coeffFun a (circleMap 0 r θ))]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have : (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖coeffFun a (circleMap 0 r θ)‖ ^ 2
      ≤ (2 * π)⁻¹ * ((2 * π - 0) * M ^ 2) :=
    mul_le_mul_of_nonneg_left hint (by positivity)
  calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖coeffFun a (circleMap 0 r θ)‖ ^ 2
      ≤ (2 * π)⁻¹ * ((2 * π - 0) * M ^ 2) := this
    _ = M ^ 2 := by
        rw [sub_zero]
        field_simp

end GaloisForLFunctions.HTGeometry
