import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeIntervals
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-! Cauchy–Schwarz for finite prime sums in logarithmic measure. -/

open MeasureTheory

namespace QH.PrimeProgressions

private lemma measurable_norm_sum_primesIoc (a : ℕ → ℂ) (x : ℝ) :
    Measurable (fun t : ℝ => ‖∑ p ∈ primesIoc x t, a p‖) := by
  have h : (fun t : ℝ => ‖∑ p ∈ primesIoc x t, a p‖) =
      (fun n : ℕ => ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ n).filter Nat.Prime, a p‖) ∘ Nat.floor := by
    funext t
    rfl
  rw [h]
  exact measurable_from_nat.comp Nat.measurable_floor

private lemma norm_sum_primesIoc_le_sum_range (a : ℕ → ℂ) (x y t : ℝ) (hty : t ≤ y) :
    ‖∑ p ∈ primesIoc x t, a p‖ ≤ ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖ := by
  refine (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _))
  intro n hn
  have hn' := (Finset.mem_filter.1 hn).1
  have h1 := (Finset.mem_Ioc.1 hn').2
  have h2 : ⌊t⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hty
  exact Finset.mem_range.2 (by omega)

private lemma integrableOn_norm_sq_sum_primesIoc_div (a : ℕ → ℂ) (x y : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => ‖∑ p ∈ primesIoc x t, a p‖ ^ 2 / t) (Set.Icc x y) := by
  set B := ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖
  refine Measure.integrableOn_of_bounded (M := B ^ 2 / x) (by simp)
    (((measurable_norm_sum_primesIoc a x).pow_const 2).div measurable_id).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
  have ht0 : 0 < t := hx.trans_le ht.1
  change ‖(‖∑ p ∈ primesIoc x t, a p‖ ^ 2 / t : ℝ)‖ ≤ B ^ 2 / x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_div₀ (by positivity)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_primesIoc_le_sum_range a x y t ht.2) 2) hx ht.1

theorem sq_integral_primeSum_div_le (a : ℕ → ℂ) (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t) ^ 2 ≤
      Real.log (y / x) * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ ^ 2 / t := by
  have hx0 : 0 < x := by linarith
  let μ := volume.restrict (Set.Ioc x y)
  let w (t : ℝ) : ℝ := |t⁻¹|
  let g (t : ℝ) : ℝ := ‖∑ p ∈ primesIoc x t, a p‖
  have hpos : ∀ᵐ t ∂μ, 0 < t :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ ht => hx0.trans ht.1
  have hw : w =ᵐ[μ] fun t : ℝ => 1 / t := hpos.mono fun t ht => by
    change |t⁻¹| = 1 / t
    rw [abs_of_nonneg (inv_nonneg.mpr ht.le), one_div]
  have hwg (k : ℕ) : (fun t => w t * g t ^ k) =ᵐ[μ] fun t => g t ^ k / t :=
    hw.mono fun t ht => by
      change w t = 1 / t at ht
      change w t * g t ^ k = g t ^ k / t
      rw [ht, one_div, div_eq_mul_inv, mul_comm]
  have hcont : ContinuousOn (fun t : ℝ => 1 / t) (Set.Icc x y) :=
    continuousOn_const.div continuousOn_id fun t ht => (hx0.trans_le ht.1).ne'
  have hiw : Integrable (fun t : ℝ => 1 / t) μ :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hig : Integrable (fun t => g t ^ 2 / t) μ :=
    (integrableOn_norm_sq_sum_primesIoc_div a x y hx0).mono_set Set.Ioc_subset_Icc_self
  have h := GaloisForLFunctions.HTGeometry.sq_integral_weighted_le (μ := μ) (w := w) (g := g)
    (fun t => abs_nonneg (t⁻¹)) measurable_id.inv.abs.aestronglyMeasurable
    (measurable_norm_sum_primesIoc a x).aestronglyMeasurable
    (hiw.congr hw.symm) (hig.congr (hwg 2).symm)
  have hwg₁ : (fun t => w t * g t) =ᵐ[μ] fun t => g t / t := by
    simpa only [pow_one] using hwg 1
  rw [integral_congr_ae hwg₁, integral_congr_ae hw, integral_congr_ae (hwg 2)] at h
  have hlog : ∫ t in x..y, 1 / t = Real.log (y / x) := integral_one_div_of_pos hx0 (by linarith)
  simpa only [μ, g, ← intervalIntegral.integral_of_le hxy, hlog] using h

end QH.PrimeProgressions
