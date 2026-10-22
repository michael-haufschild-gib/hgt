import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCalibratedPowerReciprocalAllDegreeNoGo
import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffQuadrantRH

/-!
# Finite-tail no-go for source-selected reciprocal-power carrier

Source-selected reciprocal-power carrier matches zeroth and first prime--archimedean moments,
but cannot represent any complete even-shifted moment tail. If such a match began at `2M`,
positivity would yield RH via shifted trace--Hankel positivity. Under RH, compact moment
determinacy would identify this continuous carrier with canonical Xi measure weighted by
`x^(2M)`. That is impossible: source carrier has positive mass off closed Xi thermal-node
set, whereas every weighted canonical Xi measure remains carried by that set.

An odd shift first becomes an even shift after weighting the source carrier by `x`; strict
positivity of the source support makes this a positive measure and therefore forces RH. Under RH,
the corresponding canonical odd tail is again compact and atomic. Thus no finite starting index,
of either parity, can make this fixed continuous carrier represent the complete source tail.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- Nonnegative even-power density for canonical Xi tail beginning at `2M`. -/
def xiEvenTailDensity (M : ℕ) : ℝ → NNReal := fun x =>
  ⟨x ^ (2 * M), by
    rw [show 2 * M = M * 2 by omega, pow_mul]
    exact sq_nonneg _⟩

/-- Canonical Xi compact measure weighted to represent even tail beginning at `2M`. -/
def xiEvenTailMeasure (M : ℕ) : Measure ℝ :=
  primeArchXiCompactMomentMeasure.withDensity
    (fun x => (xiEvenTailDensity M x : ENNReal))

theorem xiEvenTailDensity_coe (M : ℕ) (x : ℝ) :
    (xiEvenTailDensity M x : ℝ) = x ^ (2 * M) := rfl

/-- Every power remains integrable after canonical even-tail weighting. -/
theorem integrable_pow_xiEvenTailMeasure (M n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (xiEvenTailMeasure M) := by
  rw [xiEvenTailMeasure, integrable_withDensity_iff_integrable_smul]
  · simpa only [NNReal.smul_def, smul_eq_mul, xiEvenTailDensity_coe, ← pow_add]
      using integrable_primeArchXiCompactMomentMeasure (2 * M + n)
  · exact measurable_coe_nnreal_real_iff.mp (continuous_pow _).measurable

/-- Under RH, canonical even-tail measure has exactly shifted source moments. -/
theorem integral_pow_xiEvenTailMeasure_eq_of_riemannHypothesis
    (M n : ℕ) (hRH : RiemannHypothesis) :
    (∫ x : ℝ, x ^ n ∂xiEvenTailMeasure M) =
      normalizedPrimeArchMoment (2 * M + n) := by
  rw [xiEvenTailMeasure, integral_withDensity_eq_integral_smul]
  · rw [show (fun x : ℝ => xiEvenTailDensity M x • x ^ n) =
      fun x : ℝ => x ^ (2 * M + n) by
        funext x
        rw [NNReal.smul_def, smul_eq_mul, xiEvenTailDensity_coe, ← pow_add]]
    exact integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis hRH _
  · exact measurable_coe_nnreal_real_iff.mp (continuous_pow _).measurable

theorem xiEvenTailMeasure_finite (M : ℕ) :
    IsFiniteMeasure (xiEvenTailMeasure M) := by
  apply (integrable_const_iff_isFiniteMeasure
    (μ := xiEvenTailMeasure M) (c := (1 : ℝ)) one_ne_zero).mp
  simpa only [pow_zero] using integrable_pow_xiEvenTailMeasure M 0

theorem xiEvenTailMeasure_measure_compl_Icc_negOne_one_eq_zero (M : ℕ) :
    xiEvenTailMeasure M (Set.Icc ((0 : ℝ) - 1) (0 + 1))ᶜ = 0 := by
  apply MeasureTheory.withDensity_absolutelyContinuous
    primeArchXiCompactMomentMeasure (fun x => (xiEvenTailDensity M x : ENNReal))
  exact primeArchXiCompactMomentMeasure_measure_compl_Icc_negOne_one_eq_zero

theorem xiEvenTailMeasure_compl_xiThermalCompactNodeSet_eq_zero (M : ℕ) :
    xiEvenTailMeasure M xiThermalCompactNodeSetᶜ = 0 := by
  apply MeasureTheory.withDensity_absolutelyContinuous
    primeArchXiCompactMomentMeasure (fun x => (xiEvenTailDensity M x : ENNReal))
  exact primeArchXiCompactMomentMeasure_compl_xiThermalCompactNodeSet_eq_zero

/-- Positive measure realizing any complete even-shifted source tail proves RH. -/
theorem riemannHypothesis_of_evenShiftedPrimeArchMomentRepresentation
    (M : ℕ) {μ : Measure ℝ}
    (hmom : ∀ n : ℕ,
      normalizedPrimeArchMoment (2 * M + n) =
        ∫ x : ℝ, x ^ n ∂μ)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) :
    RiemannHypothesis := by
  apply (sequenceTraceHankelNonnegative_shiftedPrimeArchMomentTail_iff_riemannHypothesis M).mp
  intro p
  rw [sequenceTraceHankel_eq_momentFunctional]
  apply HTGeometry.momentFunctional_pow_two_nonneg
  · intro n
    simpa only [shiftedPrimeArchMomentTail] using hmom n
  · exact hint

theorem thetaCuspSourceSelectedPowerReciprocal_eq_xiEvenTailMeasure_of_match
    (M : ℕ)
    (hmatch : ∀ n : ℕ,
      normalizedPrimeArchMoment (2 * M + n) =
        ∫ x : ℝ, x ^ n
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent) :
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
        thetaCuspSourceSelectedPowerReciprocalExponent =
      xiEvenTailMeasure M := by
  let μ : Measure ℝ :=
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
      thetaCuspSourceSelectedPowerReciprocalExponent
  letI : IsFiniteMeasure μ :=
    (integrable_const_iff_isFiniteMeasure (μ := μ) (c := (1 : ℝ)) one_ne_zero).mp
      (by simpa only [pow_zero] using
        integrable_pow_thetaCuspSourceSelectedPowerReciprocal 0)
  letI : IsFiniteMeasure (xiEvenTailMeasure M) := xiEvenTailMeasure_finite M
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_evenShiftedPrimeArchMomentRepresentation M
      (by simpa only [μ] using hmatch)
      (fun n => by simpa only [μ] using
        integrable_pow_thetaCuspSourceSelectedPowerReciprocal n)
  have heq := HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := fun n => normalizedPrimeArchMoment (2 * M + n))
    (mu := xiEvenTailMeasure M) (nu := μ)
    (c := 0) (r := 1) (by norm_num : (0 : ℝ) < 1)
    (xiEvenTailMeasure_measure_compl_Icc_negOne_one_eq_zero M)
    (fun n =>
      (integral_pow_xiEvenTailMeasure_eq_of_riemannHypothesis M n hRH).symm)
    (integrable_pow_xiEvenTailMeasure M)
    (fun n => by simpa only [μ] using hmatch n)
    (fun n => by simpa only [μ] using
      integrable_pow_thetaCuspSourceSelectedPowerReciprocal n)
  simpa only [μ] using heq.symm

/-- **Even-tail no-go.** Source-selected continuous reciprocal-power carrier cannot match complete
prime--archimedean moment tail after any even finite cutoff. -/
theorem not_exists_evenTail_thetaCuspSourceSelectedPowerReciprocal_moment_matching :
    ¬ ∃ M : ℕ, ∀ n : ℕ,
      normalizedPrimeArchMoment (2 * M + n) =
        ∫ x : ℝ, x ^ n
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent := by
  rintro ⟨M, hmatch⟩
  have heq :=
    thetaCuspSourceSelectedPowerReciprocal_eq_xiEvenTailMeasure_of_match M hmatch
  have hpos := thetaCuspSourceSelectedPowerReciprocal_compl_xiThermalCompactNodeSet_pos
  rw [heq, xiEvenTailMeasure_compl_xiThermalCompactNodeSet_eq_zero] at hpos
  exact hpos.false

/-- The source-positive coordinate weighting converts an odd source tail into an even one. -/
def thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure : Measure ℝ :=
  (thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
    thetaCuspSourceSelectedPowerReciprocalExponent).withDensity
      (fun x => ENNReal.ofReal x)

theorem integrable_pow_thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n)
      thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure := by
  rw [thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (integrable_pow_thetaCuspSourceSelectedPowerReciprocal (n + 1)).congr ?_
  filter_upwards [ae_thetaCuspSourceSelectedPowerReciprocal_support_one_div_eightyOne] with x hx
  rw [ENNReal.toReal_ofReal hx.1.le, smul_eq_mul, pow_succ]
  ring

theorem integral_pow_thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure) =
      ∫ x : ℝ, x ^ (n + 1) ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
        thetaCuspSourceSelectedPowerReciprocalExponent := by
  rw [thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_thetaCuspSourceSelectedPowerReciprocal_support_one_div_eightyOne] with x hx
  rw [ENNReal.toReal_ofReal hx.1.le, smul_eq_mul, pow_succ]
  ring

/-- Odd-shift matching would yield an even shifted positive-moment representation, hence RH. -/
theorem riemannHypothesis_of_oddShiftedPrimeArchMomentRepresentation
    (M : ℕ)
    (hmatch : ∀ n : ℕ,
      normalizedPrimeArchMoment (2 * M + 1 + n) =
        ∫ x : ℝ, x ^ n
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_evenShiftedPrimeArchMomentRepresentation (M + 1)
  · intro n
    calc
      normalizedPrimeArchMoment (2 * (M + 1) + n) =
          normalizedPrimeArchMoment (2 * M + 1 + (n + 1)) := by
        congr 1
        omega
      _ = ∫ x : ℝ, x ^ (n + 1)
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent := hmatch (n + 1)
      _ = ∫ x : ℝ, x ^ n
          ∂thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure :=
        (integral_pow_thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure n).symm
  · exact integrable_pow_thetaCuspSourceSelectedPowerReciprocalXWeightedMeasure

/-- Canonical Xi compact measure weighted by its coordinate represents the odd tail. -/
def xiOddTailMeasure (M : ℕ) : Measure ℝ :=
  (xiEvenTailMeasure M).withDensity (fun x => ENNReal.ofReal x)

theorem ae_xiEvenTailMeasure_mem_zero_one (M : ℕ) :
    ∀ᵐ x : ℝ ∂xiEvenTailMeasure M, 0 ≤ x ∧ |x| ≤ 1 := by
  apply mem_ae_iff.mpr
  apply MeasureTheory.withDensity_absolutelyContinuous
    primeArchXiCompactMomentMeasure (fun x => (xiEvenTailDensity M x : ENNReal))
  exact mem_ae_iff.mp ae_primeArchXiCompactMomentMeasure_mem_zero_one

theorem integrable_pow_xiOddTailMeasure (M n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (xiOddTailMeasure M) := by
  rw [xiOddTailMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (integrable_pow_xiEvenTailMeasure M (n + 1)).congr ?_
  filter_upwards [ae_xiEvenTailMeasure_mem_zero_one M] with x hx
  rw [ENNReal.toReal_ofReal hx.1, smul_eq_mul, pow_succ]
  ring

theorem integral_pow_xiOddTailMeasure_eq_of_riemannHypothesis
    (M n : ℕ) (hRH : RiemannHypothesis) :
    (∫ x : ℝ, x ^ n ∂xiOddTailMeasure M) =
      normalizedPrimeArchMoment (2 * M + 1 + n) := by
  rw [xiOddTailMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    (∫ x : ℝ, (ENNReal.ofReal x).toReal • x ^ n ∂xiEvenTailMeasure M) =
        ∫ x : ℝ, x ^ (n + 1) ∂xiEvenTailMeasure M := by
      apply integral_congr_ae
      filter_upwards [ae_xiEvenTailMeasure_mem_zero_one M] with x hx
      rw [ENNReal.toReal_ofReal hx.1, smul_eq_mul, pow_succ]
      ring
    _ = normalizedPrimeArchMoment (2 * M + (n + 1)) :=
      integral_pow_xiEvenTailMeasure_eq_of_riemannHypothesis M (n + 1) hRH
    _ = normalizedPrimeArchMoment (2 * M + 1 + n) := by
      congr 1
      omega

theorem xiOddTailMeasure_finite (M : ℕ) :
    IsFiniteMeasure (xiOddTailMeasure M) := by
  apply (integrable_const_iff_isFiniteMeasure
    (μ := xiOddTailMeasure M) (c := (1 : ℝ)) one_ne_zero).mp
  simpa only [pow_zero] using integrable_pow_xiOddTailMeasure M 0

theorem xiOddTailMeasure_measure_compl_Icc_negOne_one_eq_zero (M : ℕ) :
    xiOddTailMeasure M (Set.Icc ((0 : ℝ) - 1) (0 + 1))ᶜ = 0 := by
  apply MeasureTheory.withDensity_absolutelyContinuous
    (xiEvenTailMeasure M) (fun x => ENNReal.ofReal x)
  exact xiEvenTailMeasure_measure_compl_Icc_negOne_one_eq_zero M

theorem xiOddTailMeasure_compl_xiThermalCompactNodeSet_eq_zero (M : ℕ) :
    xiOddTailMeasure M xiThermalCompactNodeSetᶜ = 0 := by
  apply MeasureTheory.withDensity_absolutelyContinuous
    (xiEvenTailMeasure M) (fun x => ENNReal.ofReal x)
  exact xiEvenTailMeasure_compl_xiThermalCompactNodeSet_eq_zero M

theorem thetaCuspSourceSelectedPowerReciprocal_eq_xiOddTailMeasure_of_match
    (M : ℕ)
    (hmatch : ∀ n : ℕ,
      normalizedPrimeArchMoment (2 * M + 1 + n) =
        ∫ x : ℝ, x ^ n
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent) :
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
        thetaCuspSourceSelectedPowerReciprocalExponent = xiOddTailMeasure M := by
  let μ : Measure ℝ :=
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
      thetaCuspSourceSelectedPowerReciprocalExponent
  letI : IsFiniteMeasure μ :=
    (integrable_const_iff_isFiniteMeasure (μ := μ) (c := (1 : ℝ)) one_ne_zero).mp
      (by simpa only [pow_zero] using
        integrable_pow_thetaCuspSourceSelectedPowerReciprocal 0)
  letI : IsFiniteMeasure (xiOddTailMeasure M) := xiOddTailMeasure_finite M
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_oddShiftedPrimeArchMomentRepresentation M
      (by simpa only [μ] using hmatch)
  have heq := HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := fun n => normalizedPrimeArchMoment (2 * M + 1 + n))
    (mu := xiOddTailMeasure M) (nu := μ)
    (c := 0) (r := 1) (by norm_num : (0 : ℝ) < 1)
    (xiOddTailMeasure_measure_compl_Icc_negOne_one_eq_zero M)
    (fun n =>
      (integral_pow_xiOddTailMeasure_eq_of_riemannHypothesis M n hRH).symm)
    (integrable_pow_xiOddTailMeasure M)
    (fun n => by simpa only [μ] using hmatch n)
    (fun n => by simpa only [μ] using
      integrable_pow_thetaCuspSourceSelectedPowerReciprocal n)
  simpa only [μ] using heq.symm

/-- No odd cutoff lets the fixed source-selected continuous carrier represent the full tail. -/
theorem not_exists_oddTail_thetaCuspSourceSelectedPowerReciprocal_moment_matching :
    ¬ ∃ M : ℕ, ∀ n : ℕ,
      normalizedPrimeArchMoment (2 * M + 1 + n) =
        ∫ x : ℝ, x ^ n
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent := by
  rintro ⟨M, hmatch⟩
  have heq :=
    thetaCuspSourceSelectedPowerReciprocal_eq_xiOddTailMeasure_of_match M hmatch
  have hpos := thetaCuspSourceSelectedPowerReciprocal_compl_xiThermalCompactNodeSet_pos
  rw [heq, xiOddTailMeasure_compl_xiThermalCompactNodeSet_eq_zero] at hpos
  exact hpos.false

/-- **Finite-tail no-go.** No finite cutoff makes this fixed continuous carrier represent a
complete normalized prime--archimedean moment tail. -/
theorem not_exists_tail_thetaCuspSourceSelectedPowerReciprocal_moment_matching :
    ¬ ∃ K : ℕ, ∀ n : ℕ,
      normalizedPrimeArchMoment (K + n) =
        ∫ x : ℝ, x ^ n
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent := by
  rintro ⟨K, hmatch⟩
  rcases K.even_or_odd' with ⟨M, rfl | rfl⟩
  · exact not_exists_evenTail_thetaCuspSourceSelectedPowerReciprocal_moment_matching
      ⟨M, hmatch⟩
  · exact not_exists_oddTail_thetaCuspSourceSelectedPowerReciprocal_moment_matching
      ⟨M, hmatch⟩

end

end RHTower
