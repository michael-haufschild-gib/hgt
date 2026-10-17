import GaloisForLFunctions.BiScaleUncertainty.SignedGramCutoffComparison

/-!
# Monotone quantitative saturation for each actual signed source

Optimize the full measured Gram certificate over physical partitions. Its actual
cutoff optimum is monotone, with error at most twice source energy times the
retention tail. The finite limit bounds the actual extended increment energy,
without grid zeros or an assumed energy/Gram interface. Normalized cutoff error
is explicitly inverse square root, including the zero source by total division.
These are source-dependent certificates, not uniform blind-grid constants.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n m : ℕ}

theorem signedGramCoefficient_bounds (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    0 ≤ ρ.signedGramCoefficient f ∧
      ρ.signedGramCoefficient f ≤ 2 * autocorr f 0 * collarTailMass := by
  constructor
  · exact setIntegral_nonneg measurableSet_Ioo fun y hy => (ρ.signedGramKernel_bounds f hy.1.le).1
  · have h := integral_mono_ae (ρ.integrableOn_signedGramKernel f)
      (ρ.integrableOn_mass.const_mul (2 * autocorr f 0)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        exact (ρ.signedGramKernel_bounds f hy.1.le).2)
    rw [integral_const_mul, ρ.integral_mass] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity [autocorr_zero_nonneg f]))
    apply setIntegral_mono_set integrableOn_archWeight_collar_tail
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx)).le
    · exact Filter.Eventually.of_forall fun _ hx => hx.1

def signedGramOptimalCoefficient (f : C_c(ℝ, ℝ)) (n : ℕ) : ℝ :=
  sSup (Set.range (fun ρ : PhysicalCollarPartition n => ρ.signedGramCoefficient f))

theorem signedGramCoefficient_range_bddAbove (f : C_c(ℝ, ℝ)) (n : ℕ) :
    BddAbove (Set.range (fun ρ : PhysicalCollarPartition n => ρ.signedGramCoefficient f)) :=
  ⟨2 * autocorr f 0 * collarTailMass, by rintro c ⟨ρ, rfl⟩; exact (ρ.signedGramCoefficient_bounds f).2⟩

theorem signedGramCoefficient_le_optimal (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.signedGramCoefficient f ≤ signedGramOptimalCoefficient f n :=
  le_csSup (signedGramCoefficient_range_bddAbove f n) ⟨ρ, rfl⟩

theorem signedGramOptimalCoefficient_bounds (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ signedGramOptimalCoefficient f n ∧
      signedGramOptimalCoefficient f n ≤ 2 * autocorr f 0 * collarTailMass := by
  constructor
  · exact ((equalMultiplicity n).signedGramCoefficient_bounds f).1.trans
      ((equalMultiplicity n).signedGramCoefficient_le_optimal f)
  · apply csSup_le
    · exact ⟨(equalMultiplicity n).signedGramCoefficient f, equalMultiplicity n, rfl⟩
    · rintro c ⟨ρ, rfl⟩
      exact (ρ.signedGramCoefficient_bounds f).2

/-- The current optimum itself is monotone; no running-maximum replacement is used. -/
theorem signedGramOptimalCoefficient_monotone (f : C_c(ℝ, ℝ)) :
    Monotone (signedGramOptimalCoefficient f) := by
  intro n m hm
  apply csSup_le
  · exact ⟨(equalMultiplicity n).signedGramCoefficient f, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (ρ.signedGramCoefficient_le_extend hm f).trans
      ((ρ.extend hm).signedGramCoefficient_le_optimal f)

theorem signedGramOptimalCoefficient_sub_le_tail (f : C_c(ℝ, ℝ)) (hm : n ≤ m) :
    signedGramOptimalCoefficient f m - signedGramOptimalCoefficient f n ≤
      2 * autocorr f 0 * collarCutoffTailMass n := by
  have h : signedGramOptimalCoefficient f m ≤
      signedGramOptimalCoefficient f n + 2 * autocorr f 0 * collarCutoffTailMass n := by
    apply csSup_le
    · exact ⟨(equalMultiplicity m).signedGramCoefficient f, equalMultiplicity m, rfl⟩
    · rintro c ⟨η, rfl⟩
      have hc := η.signedGramCoefficient_sub_retract_le_tail hm f
      have hp := (η.retract hm).signedGramCoefficient_le_optimal f
      linarith only [hc, hp]
  linarith only [h]

theorem signedGramOptimalCoefficient_bddAbove (f : C_c(ℝ, ℝ)) :
    BddAbove (Set.range (signedGramOptimalCoefficient f)) :=
  ⟨2 * autocorr f 0 * collarTailMass, by rintro c ⟨n, rfl⟩; exact (signedGramOptimalCoefficient_bounds f n).2⟩

def limitingSignedGramCoefficient (f : C_c(ℝ, ℝ)) : ℝ := ⨆ n, signedGramOptimalCoefficient f n

theorem signedGramOptimalCoefficient_le_limit (f : C_c(ℝ, ℝ)) (n : ℕ) :
    signedGramOptimalCoefficient f n ≤ limitingSignedGramCoefficient f :=
  le_ciSup (signedGramOptimalCoefficient_bddAbove f) n

theorem limitingSignedGramCoefficient_bounds (f : C_c(ℝ, ℝ)) :
    0 ≤ limitingSignedGramCoefficient f ∧
      limitingSignedGramCoefficient f ≤ 2 * autocorr f 0 * collarTailMass :=
  ⟨(signedGramOptimalCoefficient_bounds f 0).1.trans (signedGramOptimalCoefficient_le_limit f 0),
    ciSup_le (fun n => (signedGramOptimalCoefficient_bounds f n).2)⟩

theorem signedGramOptimalCoefficient_tendsto (f : C_c(ℝ, ℝ)) :
    Filter.Tendsto (signedGramOptimalCoefficient f) Filter.atTop (nhds (limitingSignedGramCoefficient f)) :=
  tendsto_atTop_ciSup (signedGramOptimalCoefficient_monotone f) (signedGramOptimalCoefficient_bddAbove f)

theorem limitingSignedGramCoefficient_sub_bounds (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ limitingSignedGramCoefficient f - signedGramOptimalCoefficient f n ∧
      limitingSignedGramCoefficient f - signedGramOptimalCoefficient f n ≤
        2 * autocorr f 0 * collarCutoffTailMass n := by
  have hl := signedGramOptimalCoefficient_le_limit f n
  have hu : limitingSignedGramCoefficient f ≤
      signedGramOptimalCoefficient f n + 2 * autocorr f 0 * collarCutoffTailMass n := by
    apply ciSup_le
    intro m
    rcases le_total n m with hnm | hmn
    · have h := signedGramOptimalCoefficient_sub_le_tail f hnm
      linarith only [h]
    · exact (signedGramOptimalCoefficient_monotone f hmn).trans
        (le_add_of_nonneg_right (by positivity [autocorr_zero_nonneg f, collarCutoffTailMass_nonneg n]))
  constructor <;> linarith only [hl, hu]

/-- Optimization preserves the actual finite-window extended-energy receiver. -/
theorem signedGramOptimalCoefficient_source_energy (f : C_c(ℝ, ℝ)) (n : ℕ) :
    ENNReal.ofReal (signedGramOptimalCoefficient f n) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n), continuousArchIncrementDensity (compactAutocorrKernel f) x := by
  by_cases ht : (∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
      continuousArchIncrementDensity (compactAutocorrKernel f) x) = ⊤
  · rw [ht]
    exact le_top
  · rw [ENNReal.ofReal_le_iff_le_toReal ht]
    apply csSup_le
    · exact ⟨(equalMultiplicity n).signedGramCoefficient f, equalMultiplicity n, rfl⟩
    · rintro c ⟨ρ, rfl⟩
      exact (ENNReal.ofReal_le_iff_le_toReal ht).1 (ρ.signedGramCoefficient_source_energy f)

/-- Unconditional infinite-cutoff certificate for every actual compact continuous source. -/
theorem limitingSignedGramCoefficient_source_energy (f : C_c(ℝ, ℝ)) :
    ENNReal.ofReal (limitingSignedGramCoefficient f) ≤
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f) x := by
  by_cases ht : (∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f) x) = ⊤
  · rw [ht]
    exact le_top
  · rw [ENNReal.ofReal_le_iff_le_toReal ht]
    apply ciSup_le
    intro n
    apply (ENNReal.ofReal_le_iff_le_toReal ht).1
    exact (signedGramOptimalCoefficient_source_energy f n).trans
      (lintegral_mono_set (show Ioo 0 (logarithmicCollarEndpoint n) ⊆ Ioi 0 from fun _ hx => hx.1))

theorem signedGramOptimalCoefficient_le_energy (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (n : ℕ) :
    signedGramOptimalCoefficient f n ≤ biScaleLevyEnergy f := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).signedGramCoefficient f, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact ρ.signedGramCoefficient_le_energy f hf

theorem limitingSignedGramCoefficient_le_energy (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) : limitingSignedGramCoefficient f ≤ biScaleLevyEnergy f :=
  ciSup_le (signedGramOptimalCoefficient_le_energy f hf)

theorem signedGramNormalizedCoefficient_monotone (f : C_c(ℝ, ℝ)) :
    Monotone (fun n => signedGramOptimalCoefficient f n / autocorr f 0) :=
  fun _ _ h => div_le_div_of_nonneg_right (signedGramOptimalCoefficient_monotone f h) (autocorr_zero_nonneg f)

/-- The normalized retention estimate also covers zero source energy by total division. -/
theorem signedGramNormalizedCoefficient_sub_bounds (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ limitingSignedGramCoefficient f / autocorr f 0 - signedGramOptimalCoefficient f n / autocorr f 0 ∧
      limitingSignedGramCoefficient f / autocorr f 0 - signedGramOptimalCoefficient f n / autocorr f 0 ≤
        2 * collarCutoffTailMass n := by
  have h := limitingSignedGramCoefficient_sub_bounds f n
  constructor
  · rw [← sub_div]
    exact div_nonneg h.1 (autocorr_zero_nonneg f)
  · by_cases hR : autocorr f 0 = 0
    · simp only [hR, div_zero, sub_self]
      exact mul_nonneg (by norm_num) (collarCutoffTailMass_nonneg n)
    · have hRp : 0 < autocorr f 0 := lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm hR)
      rw [← sub_div]
      apply (div_le_iff₀ hRp).2
      nlinarith only [h.2]

/-- Explicit inverse-square-root error in the literal node cutoff N=n+2. -/
theorem signedGramNormalizedCoefficient_quantitative_saturation (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ limitingSignedGramCoefficient f / autocorr f 0 - signedGramOptimalCoefficient f n / autocorr f 0 ∧
      limitingSignedGramCoefficient f / autocorr f 0 - signedGramOptimalCoefficient f n / autocorr f 0 ≤
        8 * Real.exp (logarithmicCollarRadius / 2) /
          (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) := by
  have h := signedGramNormalizedCoefficient_sub_bounds f n
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ 2 * (4 * Real.exp (logarithmicCollarRadius / 2) /
        (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2)))) :=
      mul_le_mul_of_nonneg_left (collarCutoffTailMass_le_inverse_sqrt n) (by norm_num)
    _ = _ := by ring

/-- The finite and limiting measured-Gram certificates both bound actual normalized energy. -/
theorem signedGram_actual_source_certificate (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (n : ℕ) :
    signedGramOptimalCoefficient f n / autocorr f 0 ≤ limitingSignedGramCoefficient f / autocorr f 0 ∧
      limitingSignedGramCoefficient f / autocorr f 0 ≤ biScaleLevyEnergy f / autocorr f 0 :=
  ⟨div_le_div_of_nonneg_right (signedGramOptimalCoefficient_le_limit f n) (autocorr_zero_nonneg f),
    div_le_div_of_nonneg_right (limitingSignedGramCoefficient_le_energy f hf) (autocorr_zero_nonneg f)⟩

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
