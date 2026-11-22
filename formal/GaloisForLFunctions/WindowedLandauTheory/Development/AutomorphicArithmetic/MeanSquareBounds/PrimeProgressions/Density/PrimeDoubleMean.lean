import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeMeanValue
import GaloisForLFunctions.WindowedLandauTheory.CesaroIncrementBounds

/-! Average the hybrid prime mean square over the upper prime cutoff. -/

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Finset
open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

def primeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N y τ : ℝ) : ℂ :=
  ∑ p ∈ primesIoc N y, ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(τ * I))

theorem norm_cpow_le (n : ℕ) (τ : ℝ) : ‖(n : ℂ) ^ (-(τ * I))‖ ≤ 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · by_cases h : (-(τ * I) : ℂ) = 0
    · rw [h]; simp
    · rw [Nat.cast_zero, Complex.zero_cpow h]; simp
  · rw [Complex.norm_natCast_cpow_of_pos hn]; simp

theorem integrable_primeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N M T : ℝ) (hN : 1 ≤ N) :
    Integrable (Function.uncurry fun τ y : ℝ => ‖primeSum χ N y τ‖ ^ 2 / y)
      ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioc N M))) := by
  have hm1 : Measurable (fun x : ℝ × ℕ => ∑ p ∈ (Finset.Ioc ⌊N⌋₊ x.2).filter Nat.Prime,
      ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(x.1 * I))) := by
    refine measurable_from_prod_countable_left fun n => ?_
    show Measurable (fun τ : ℝ => ∑ p ∈ (Finset.Ioc ⌊N⌋₊ n).filter Nat.Prime,
      ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(τ * I)))
    refine Continuous.measurable (continuous_finsetSum _ fun p hp => ?_)
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hp0))
  have hm0 : Measurable (fun x : ℝ × ℝ => ((x.1, ⌊x.2⌋₊) : ℝ × ℕ)) :=
    measurable_fst.prodMk (Nat.measurable_floor.comp measurable_snd)
  have hm2 : Measurable (fun x : ℝ × ℝ => primeSum χ N x.2 x.1) := by
    have := hm1.comp hm0
    simpa only [Function.comp_def, primeSum, primesIoc] using this
  have hm3 : Measurable (Function.uncurry fun τ y : ℝ => ‖primeSum χ N y τ‖ ^ 2 / y) :=
    (hm2.norm.pow_const 2).div measurable_snd
  refine Integrable.of_bound hm3.aestronglyMeasurable
    ((∑ p ∈ primesIoc N M, ‖(Real.log p : ℂ) / p‖) ^ 2) ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)).mono ?_
  rintro ⟨τ, y⟩ ⟨-, hy1, hy2⟩
  simp only at hy1 hy2
  have hb : ‖primeSum χ N y τ‖ ≤ ∑ p ∈ primesIoc N M, ‖(Real.log p : ℂ) / p‖ := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _))
    · rw [norm_mul, norm_mul, mul_assoc]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) (norm_cpow_le p τ))
    · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hy2))
  simp only [Function.uncurry]
  rw [Real.norm_of_nonneg (div_nonneg (by positivity) (by linarith))]
  exact (div_le_self (by positivity) (by linarith)).trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

theorem sum_log_div_le : ∃ CM : ℝ, 0 ≤ CM ∧ ∀ N y : ℝ, 1 ≤ y →
    ∑ p ∈ primesIoc N y, (p : ℝ) * ‖(Real.log p : ℂ) / p‖ ^ 2 / Real.log p ≤ Real.log y + CM := by
  refine ⟨Real.log 4 + 4, by positivity, fun N y hy => ?_⟩
  have h1 : ∑ p ∈ primesIoc N y, (p : ℝ) * ‖(Real.log p : ℂ) / p‖ ^ 2 / Real.log p ≤
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) := by
    refine (le_of_eq (Finset.sum_congr rfl fun p hp => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => Λ n / (n : ℝ)) ?_
        fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    · have hpp := (Finset.mem_filter.1 hp).2
      have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      rw [vonMangoldt_apply_prime hpp, norm_div, Complex.norm_real, Complex.norm_natCast,
        Real.norm_of_nonneg hl.le]
      field_simp
    · intro p hp
      have := Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1
      exact Finset.mem_Icc.2 ⟨by omega, this.2⟩
  exact h1.trans (WindowedLandauTheory.sum_Icc_vonMangoldt_div_le hy)

theorem prime_double_mean_le : ∃ C CM : ℝ, 0 < C ∧ 0 ≤ CM ∧ ∀ (q : ℕ) [NeZero q] (T N M : ℝ), 1 ≤ T → 1 ≤ N → N ≤ M →
    (2 * q * T) ^ 2 ≤ N →
    ∑ χ : DirichletCharacter ℂ q, (∫ τ in (-T)..T, ∫ y in N..M, ‖primeSum χ N y τ‖ ^ 2 / y) ≤
      C * (Real.log M + CM) * Real.log M := by
  obtain ⟨C, hC, H⟩ := prime_mean_value
  obtain ⟨CM, hCM, HM⟩ := sum_log_div_le
  refine ⟨C, CM, hC, hCM, fun q _ T N M hT hN hNM hq => ?_⟩
  have hT' : -T ≤ T := by linarith
  simp only [intervalIntegral.integral_of_le hT', intervalIntegral.integral_of_le hNM]
  have hI := fun χ : DirichletCharacter ℂ q => integrable_primeSum χ N M T hN
  simp only [fun χ => integral_integral_swap (hI χ)]
  have hJ : ∀ χ : DirichletCharacter ℂ q, Integrable (fun y : ℝ =>
      ∫ τ in Set.Ioc (-T) T, ‖primeSum χ N y τ‖ ^ 2 / y) (volume.restrict (Set.Ioc N M)) :=
    fun χ => (hI χ).integral_prod_right
  rw [← integral_finsetSum _ (fun χ _ => hJ χ)]
  have hlM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hc : IntegrableOn (fun y : ℝ => C * (Real.log M + CM) * y⁻¹) (Set.Ioc N M) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => by
      have := hy.1; simp only [id]; linarith)
  calc _ ≤ ∫ y in Set.Ioc N M, C * (Real.log M + CM) * y⁻¹ := by
        refine setIntegral_mono_on (integrable_finsetSum _
          (fun χ _ => hJ χ)) hc measurableSet_Ioc fun y hy => ?_
        have hy1 : 1 ≤ y := by linarith [hy.1]
        simp only [integral_div]
        rw [← Finset.sum_div, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h1 := H q T N y (fun p => (Real.log p : ℂ) / p) hT hq
        simp only [intervalIntegral.integral_of_le hT'] at h1
        refine h1.trans (mul_le_mul_of_nonneg_left ((HM N y hy1).trans ?_) hC.le)
        have := Real.log_le_log (by linarith) hy.2
        linarith
    _ = C * (Real.log M + CM) * Real.log (M / N) := by
        rw [← intervalIntegral.integral_of_le hNM, intervalIntegral.integral_const_mul,
          integral_inv_of_pos (by linarith) (by linarith)]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (by linarith) (by linarith))
          (div_le_self (by linarith) hN)) (by positivity)

end QH.PrimeProgressions
