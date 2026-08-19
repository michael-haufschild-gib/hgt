import GaloisForLFunctions.HTGeometry.GutzmerIdentity

/-!
# Gutzmer's identity from an absolutely convergent power series

The circle mean of `‖∑ aₙ zⁿ‖²` at radius `r` is `∑ ‖aₙ‖² r^{2n}` as soon as the coefficient
series converges absolutely at some radius `ρ > r`.  This is the coefficient-side form of
Gutzmer's identity: no analyticity on a *fixed* disk is assumed, only a radius of absolute
convergence strictly larger than the circle being used.
-/

open Real Filter Topology Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Absolute convergence at radius `ρ` gives absolute convergence at every smaller radius. -/
theorem summable_norm_mul_pow_of_le {a : ℕ → ℂ} {r ρ : ℝ} (hr0 : 0 ≤ r) (hrρ : r ≤ ρ)
    (ha : Summable fun n => ‖a n‖ * ρ ^ n) : Summable fun n => ‖a n‖ * r ^ n := by
  refine ha.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrρ n) (norm_nonneg _)

theorem coeff_ofScalars (a : ℕ → ℂ) (n : ℕ) :
    (FormalMultilinearSeries.ofScalars ℂ a).coeff n = a n := by
  rw [FormalMultilinearSeries.coeff, show (1 : Fin n → ℂ) = fun _ => (1 : ℂ) from rfl,
    FormalMultilinearSeries.ofScalars_apply_eq]
  simp

theorem partialSum_ofScalars (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ a).partialSum N z
      = ∑ k ∈ Finset.range N, a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp

/-- The sum of a power series with coefficients `a`. -/
def powerSeriesSum (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, a n * z ^ n

/-- **Gutzmer's identity from the coefficients.** -/
theorem hasSum_gutzmer_of_summable_norm {a : ℕ → ℂ} {r ρ : ℝ} (hr0 : 0 ≤ r)
    (hrρ : r < ρ) (ha : Summable fun n => ‖a n‖ * ρ ^ n) :
    HasSum (fun n => ‖a n‖ ^ 2 * r ^ (2 * n))
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
        ‖powerSeriesSum a (circleMap 0 r θ)‖ ^ 2) := by
  classical
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hnorm : ∀ n, ‖p n‖ = ‖a n‖ := fun n => FormalMultilinearSeries.ofScalars_norm ℂ a n
  have hρ0 : 0 ≤ ρ := le_trans hr0 hrρ.le
  have hrad : ((Real.toNNReal ρ : NNReal) : ℝ≥0∞) ≤ p.radius := by
    refine FormalMultilinearSeries.le_radius_of_summable_norm p ?_
    refine ha.congr fun n => ?_
    simp [hnorm, Real.coe_toNNReal ρ hρ0]
  have hlt : ((Real.toNNReal r : NNReal) : ℝ≥0∞) < p.radius := by
    refine lt_of_lt_of_le ?_ hrad
    have hlt' : (Real.toNNReal r) < (Real.toNNReal ρ) := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r hr0, Real.coe_toNNReal ρ hρ0]
      exact hrρ
    exact_mod_cast hlt'
  have hsr : Summable fun n => ‖a n‖ * r ^ n := summable_norm_mul_pow_of_le hr0 hrρ.le ha
  have huniform : TendstoUniformlyOn (fun N θ => p.partialSum N (circleMap 0 r θ))
      (fun θ => powerSeriesSum a (circleMap 0 r θ)) atTop Set.univ := by
    have hbound : ∀ (n : ℕ) (θ : ℝ), θ ∈ (Set.univ : Set ℝ) →
        ‖a n * (circleMap 0 r θ) ^ n‖ ≤ ‖a n‖ * r ^ n := by
      intro n θ _
      rw [norm_mul, norm_pow, norm_circleMap_zero, abs_of_nonneg hr0]
    have huni := tendstoUniformlyOn_tsum_nat (u := fun n => ‖a n‖ * r ^ n)
      (f := fun (n : ℕ) (θ : ℝ) => a n * (circleMap 0 r θ) ^ n) hsr hbound
    have hlimeq : (fun θ : ℝ => ∑' n : ℕ, a n * (circleMap 0 r θ) ^ n)
        = fun θ : ℝ => powerSeriesSum a (circleMap 0 r θ) := rfl
    rw [hlimeq] at huni
    refine TendstoUniformlyOn.congr huni ?_
    filter_upwards with N
    intro θ _
    simp only [hp]
    rw [partialSum_ofScalars]
  have htend := tendsto_integral_normSq_partialSum_of_radius_of_uniform hr0 hlt huniform
  have htend' : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N, ‖p.coeff k‖ ^ 2 * r ^ (2 * k)) Filter.atTop
      (nhds ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
        ‖powerSeriesSum a (circleMap 0 r θ)‖ ^ 2)) := by
    have h := htend.const_mul ((2 * π)⁻¹)
    simpa only [circleAverage_normSq_partialSum p r] using h
  have hmono : Monotone (fun N => ∑ k ∈ Finset.range N, ‖p.coeff k‖ ^ 2 * r ^ (2 * k)) := by
    refine monotone_nat_of_le_succ fun n => ?_
    rw [Finset.sum_range_succ]
    have : 0 ≤ ‖p.coeff n‖ ^ 2 * r ^ (2 * n) := by positivity
    linarith
  have hsummable : Summable (fun k => ‖p.coeff k‖ ^ 2 * r ^ (2 * k)) :=
    summable_of_sum_range_le (fun n => by positivity) (fun n => hmono.ge_of_tendsto htend' n)
  have hts := hsummable.hasSum
  rw [tendsto_nhds_unique hsummable.hasSum.tendsto_sum_nat htend'] at hts
  refine hts.congr_fun fun n => ?_
  rw [coeff_ofScalars]

end

end GaloisForLFunctions.HTGeometry
