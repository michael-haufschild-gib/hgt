import GaloisForLFunctions.BiScaleUncertainty.RegularizedGramIteration

/-!
# Monotone quantitative producers reaching the full signed-Gram limit

At each cutoff an explicitly budgeted finite iteration produces a physical
partition. Comparing it with the previous cutoff's physical extension makes
the original source coefficients monotone. The allocation error vanishes
faster than the certified cutoff tail, identifying the produced limit with
the full measured-Gram optimum.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section

def quantitativeGramLadder (f : C_c(ℝ, ℝ)) : (n : ℕ) → PhysicalCollarPartition n
  | 0 => quantitativeGramProducer f 0 0
  | n + 1 =>
      let old := (quantitativeGramLadder f n).extend (Nat.le_succ n)
      let fresh := quantitativeGramProducer f (n + 1) (n + 1)
      if old.signedGramCoefficient f ≤ fresh.signedGramCoefficient f then fresh else old

def quantitativeGramCoefficient (f : C_c(ℝ, ℝ)) (n : ℕ) : ℝ :=
  (quantitativeGramLadder f n).signedGramCoefficient f

theorem producer_le_quantitativeGramCoefficient (f : C_c(ℝ, ℝ)) (n : ℕ) :
    (quantitativeGramProducer f n n).signedGramCoefficient f ≤ quantitativeGramCoefficient f n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    change _ ≤ (if _ then _ else _).signedGramCoefficient f
    split_ifs with h
    · exact le_rfl
    · exact (lt_of_not_ge h).le

theorem quantitativeGramCoefficient_monotone (f : C_c(ℝ, ℝ)) :
    Monotone (quantitativeGramCoefficient f) := by
  apply monotone_nat_of_le_succ
  intro n
  have he := (quantitativeGramLadder f n).signedGramCoefficient_le_extend (Nat.le_succ n) f
  change quantitativeGramCoefficient f n ≤ (if _ then _ else _).signedGramCoefficient f
  split_ifs with h
  · exact he.trans h
  · exact he

theorem quantitativeGramCoefficient_bounds (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ quantitativeGramCoefficient f n ∧ quantitativeGramCoefficient f n ≤ signedGramOptimalCoefficient f n :=
  ⟨((quantitativeGramLadder f n).signedGramCoefficient_bounds f).1,
    (quantitativeGramLadder f n).signedGramCoefficient_le_optimal f⟩

theorem quantitativeGramCoefficient_allocation_error (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ signedGramOptimalCoefficient f n - quantitativeGramCoefficient f n ∧
    signedGramOptimalCoefficient f n - quantitativeGramCoefficient f n ≤
      autocorr f 0 * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) := by
  have hp := quantitativeGramProducer_error f n n
  have hl := producer_le_quantitativeGramCoefficient f n
  have hu := (quantitativeGramCoefficient_bounds f n).2
  constructor <;> linarith only [hp.2, hl, hu]

theorem quantitativeGramCoefficient_bddAbove (f : C_c(ℝ, ℝ)) :
    BddAbove (Set.range (quantitativeGramCoefficient f)) := by
  refine ⟨2 * autocorr f 0 * collarTailMass, ?_⟩
  rintro c ⟨n, rfl⟩
  exact ((quantitativeGramLadder f n).signedGramCoefficient_bounds f).2

/-- The actual produced sequence reaches the optimized infinite-cutoff value. -/
theorem quantitativeGramCoefficient_tendsto (f : C_c(ℝ, ℝ)) :
    Tendsto (quantitativeGramCoefficient f) atTop (nhds (limitingSignedGramCoefficient f)) := by
  have hE : Tendsto (fun n : ℕ => autocorr f 0 * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (autocorr f 0 * (logarithmicCollarRadius + 1))
  have hlo := (signedGramOptimalCoefficient_tendsto f).sub hE
  rw [sub_zero] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo (signedGramOptimalCoefficient_tendsto f)
  · intro n
    have h := (quantitativeGramCoefficient_allocation_error f n).2
    linarith only [h]
  · exact fun n => (quantitativeGramCoefficient_bounds f n).2

theorem iSup_quantitativeGramCoefficient (f : C_c(ℝ, ℝ)) :
    (⨆ n, quantitativeGramCoefficient f n) = limitingSignedGramCoefficient f :=
  tendsto_nhds_unique
    (tendsto_atTop_ciSup (quantitativeGramCoefficient_monotone f) (quantitativeGramCoefficient_bddAbove f))
    (quantitativeGramCoefficient_tendsto f)

theorem quantitativeGramCoefficient_limiting_error (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ limitingSignedGramCoefficient f - quantitativeGramCoefficient f n ∧
    limitingSignedGramCoefficient f - quantitativeGramCoefficient f n ≤
      autocorr f 0 * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) +
        2 * autocorr f 0 * collarCutoffTailMass n := by
  have ha := quantitativeGramCoefficient_allocation_error f n
  have ht := limitingSignedGramCoefficient_sub_bounds f n
  constructor <;> linarith only [ha.1, ha.2, ht.1, ht.2]

theorem quantitativeGramNormalizedCoefficient_monotone (f : C_c(ℝ, ℝ)) :
    Monotone (fun n => quantitativeGramCoefficient f n / autocorr f 0) :=
  fun _ _ h => div_le_div_of_nonneg_right (quantitativeGramCoefficient_monotone f h) (autocorr_zero_nonneg f)

theorem quantitativeGramNormalizedCoefficient_tendsto (f : C_c(ℝ, ℝ)) :
    Tendsto (fun n => quantitativeGramCoefficient f n / autocorr f 0) atTop
      (nhds (limitingSignedGramCoefficient f / autocorr f 0)) :=
  (quantitativeGramCoefficient_tendsto f).div_const _

theorem quantitativeGramNormalizedCoefficient_error (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ limitingSignedGramCoefficient f / autocorr f 0 - quantitativeGramCoefficient f n / autocorr f 0 ∧
    limitingSignedGramCoefficient f / autocorr f 0 - quantitativeGramCoefficient f n / autocorr f 0 ≤
      (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) +
        8 * Real.exp (logarithmicCollarRadius / 2) /
          (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) := by
  have ha := quantitativeGramCoefficient_allocation_error f n
  have hA : (signedGramOptimalCoefficient f n - quantitativeGramCoefficient f n) / autocorr f 0 ≤
      (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) := by
    by_cases hR : autocorr f 0 = 0
    · rw [hR, div_zero]
      positivity [logarithmicCollarRadius_pos]
    · have hRp := lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm hR)
      apply (div_le_iff₀ hRp).2
      simpa only [mul_div_assoc, mul_comm, mul_left_comm] using ha.2
  have hn := div_nonneg ha.1 (autocorr_zero_nonneg f)
  rw [sub_div] at hA hn
  have ht := signedGramNormalizedCoefficient_quantitative_saturation f n
  constructor <;> linarith only [hA, hn, ht.1, ht.2]

/-- Actual compact continuous sources, including zero and infinite source energy. -/
theorem quantitativeGramCoefficient_source_energy (f : C_c(ℝ, ℝ)) (n : ℕ) :
    ENNReal.ofReal (quantitativeGramCoefficient f n) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n), continuousArchIncrementDensity (compactAutocorrKernel f) x :=
  (quantitativeGramLadder f n).signedGramCoefficient_source_energy f

/-- Monotone produced lower bounds with unconditional allocation and cutoff errors. -/
theorem quantitativeGram_source_certificate (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (n : ℕ) :
    quantitativeGramCoefficient f n / autocorr f 0 ≤ limitingSignedGramCoefficient f / autocorr f 0 ∧
    limitingSignedGramCoefficient f / autocorr f 0 ≤ biScaleLevyEnergy f / autocorr f 0 ∧
    limitingSignedGramCoefficient f / autocorr f 0 - quantitativeGramCoefficient f n / autocorr f 0 ≤
      (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) +
        8 * Real.exp (logarithmicCollarRadius / 2) /
          (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) := by
  have he := quantitativeGramNormalizedCoefficient_error f n
  exact ⟨sub_nonneg.mp he.1, (signedGram_actual_source_certificate f hf n).2, he.2⟩

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
