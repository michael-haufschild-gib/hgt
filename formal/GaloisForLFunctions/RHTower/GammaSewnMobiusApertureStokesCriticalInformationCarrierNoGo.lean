import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalInformationSchurDepletion

/-!
# Critical information carrier no-go

The scalar first-information depletion is lifted to the exact source carrier. Raw critical Stokes
measure splits coefficientwise into two positive measures on identical prime-power labels and
squared reciprocal-gap nodes:

raw carrier = information-depleted carrier + information carrier.

The depleted carrier remains finite, compact, positive, and has explicit moments, but its zeroth
moment still exceeds the complete prime--archimedean seam. Hence its compact Markov germ cannot
equal the completed seam germ. Equivalently, critical information coenergy is strictly smaller
than the raw mass excess, and any further completed correction has strictly negative mass.

All statements are unconditional and preserve prime labels and valuation multiplicity.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

theorem criticalDepletedWeight_add_informationTerm
    (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk +
        sourceHorizontalStokesConditionedInformationTerm (1 / 2) pk =
      RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk := by
  rw [gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight,
    gammaSewnMobiusApertureStokesCriticalInformationFactor,
    sourceHorizontalStokesConditionedInformationTerm,
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight]
  ring

def criticalInformationDepletedCarrier : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.sum fun pk : Nat.Primes × ℕ =>
    ENNReal.ofReal
        (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk) •
      MeasureTheory.Measure.dirac
        (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk)

def criticalInformationCarrier : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.sum fun pk : Nat.Primes × ℕ =>
    ENNReal.ofReal
        (sourceHorizontalStokesConditionedInformationTerm (1 / 2) pk) •
      MeasureTheory.Measure.dirac
        (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk)

theorem criticalSquaredCarrier_eq_depleted_add_information :
    RHTower.gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier =
      criticalInformationDepletedCarrier + criticalInformationCarrier := by
  rw [RHTower.gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier,
    RHTower.gammaSewnMobiusApertureStokesSquaredCompactCarrier,
    criticalInformationDepletedCarrier, criticalInformationCarrier,
    MeasureTheory.Measure.sum_add_sum]
  congr 1
  funext pk
  rw [← add_smul,
    ← ENNReal.ofReal_add
      (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk).le
      (sourceHorizontalStokesConditionedInformationTerm_pos
        (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num) pk).le,
    criticalDepletedWeight_add_informationTerm]

theorem integrable_one_criticalInformationDepletedCarrier :
    MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
      criticalInformationDepletedCarrier := by
  rw [criticalInformationDepletedCarrier]
  apply MeasureTheory.integrable_sum_dirac
    (fun pk => by simp [ENNReal.ofReal_ne_top])
  apply
    summable_gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight.congr
  intro pk
  rw [ENNReal.toReal_ofReal
    (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk).le]
  simp

theorem criticalInformationDepletedCarrier_finite :
    MeasureTheory.IsFiniteMeasure criticalInformationDepletedCarrier := by
  exact (MeasureTheory.integrable_const_iff_isFiniteMeasure one_ne_zero).mp
    integrable_one_criticalInformationDepletedCarrier

theorem ae_criticalInformationDepletedCarrier_mem_compact :
    ∀ᵐ y : ℝ ∂criticalInformationDepletedCarrier,
      0 ≤ y ∧ |y| ≤ ((Real.log 2)⁻¹) ^ 2 := by
  rw [criticalInformationDepletedCarrier, MeasureTheory.Measure.ae_sum_iff]
  intro pk
  apply MeasureTheory.Measure.ae_smul_measure
  exact (MeasureTheory.ae_dirac_iff
    (measurableSet_Ici.inter
      (measurableSet_le measurable_id.abs measurable_const))).2
    ⟨(RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
        (by norm_num) pk).le,
      by
        change |RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
          (1 / 2) pk| ≤ ((Real.log 2)⁻¹) ^ 2
        rw [abs_of_pos
          (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
            (by norm_num) pk)]
        exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
          (by norm_num) (by norm_num) pk⟩

theorem integrable_pow_criticalInformationDepletedCarrier (n : ℕ) :
    MeasureTheory.Integrable (fun y : ℝ => y ^ n)
      criticalInformationDepletedCarrier := by
  letI : MeasureTheory.IsFiniteMeasure criticalInformationDepletedCarrier :=
    criticalInformationDepletedCarrier_finite
  refine MeasureTheory.Integrable.of_bound
    (continuous_id.pow n).aestronglyMeasurable
    ((((Real.log 2)⁻¹) ^ 2) ^ n) ?_
  filter_upwards [ae_criticalInformationDepletedCarrier_mem_compact] with y hy
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg y) hy.2 n

theorem integral_pow_criticalInformationDepletedCarrier_eq_tsum (n : ℕ) :
    ∫ y : ℝ, y ^ n ∂criticalInformationDepletedCarrier =
      ∑' pk : Nat.Primes × ℕ,
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk *
          RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
            (1 / 2) pk ^ n := by
  rw [criticalInformationDepletedCarrier,
    MeasureTheory.integral_sum_dirac
      (fun pk => by simp [ENNReal.ofReal_ne_top])]
  apply tsum_congr
  intro pk
  rw [ENNReal.toReal_ofReal
    (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk).le]
  simp only [smul_eq_mul]

theorem normalizedPrimeArchMoment_zero_lt_integral_criticalInformationDepletedCarrier :
    RHTower.normalizedPrimeArchMoment 0 <
      ∫ y : ℝ, y ^ 0 ∂criticalInformationDepletedCarrier := by
  rw [integral_pow_criticalInformationDepletedCarrier_eq_tsum]
  simp only [pow_zero, mul_one]
  exact normalizedPrimeArchMoment_zero_lt_tsum_criticalInformationDepletedWeight

def CriticalInformationDepletedMomentIdentification : Prop :=
  RHTower.completedSeamMomentGerm =ᶠ[nhds 0]
    RHTower.compactMarkovTransform criticalInformationDepletedCarrier

theorem not_criticalInformationDepletedMomentIdentification :
    ¬ CriticalInformationDepletedMomentIdentification := by
  intro h
  have hmass :=
    RHTower.normalizedPrimeArchMoment_zero_eq_measureReal_univ_of_compactMarkovGerm
      criticalInformationDepletedCarrier h
  have hzero : RHTower.normalizedPrimeArchMoment 0 =
      ∫ y : ℝ, y ^ 0 ∂criticalInformationDepletedCarrier := by
    rw [hmass]
    simp [MeasureTheory.integral_const]
  linarith [normalizedPrimeArchMoment_zero_lt_integral_criticalInformationDepletedCarrier]

theorem criticalSquaredMass_eq_depletedMass_add_informationCoenergy :
    (∑' pk : Nat.Primes × ℕ,
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk) =
      (∑' pk : Nat.Primes × ℕ,
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk) +
        sourceHorizontalStokesConditionedInformationCoenergy (1 / 2) := by
  rw [sourceHorizontalStokesConditionedInformationCoenergy,
    ← summable_gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight.tsum_add
      (summable_sourceHorizontalStokesConditionedInformationTerm
        (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num))]
  exact tsum_congr (fun pk => (criticalDepletedWeight_add_informationTerm pk).symm)

theorem criticalInformationCoenergy_lt_rawMassExcess :
    sourceHorizontalStokesConditionedInformationCoenergy (1 / 2) <
      (∑' pk : Nat.Primes × ℕ,
          RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk) -
        RHTower.normalizedPrimeArchMoment 0 := by
  rw [criticalSquaredMass_eq_depletedMass_add_informationCoenergy]
  linarith [normalizedPrimeArchMoment_zero_lt_tsum_criticalInformationDepletedWeight]

theorem criticalInformationAdditionalCarrierCorrection_mass_neg
    {C : ℝ}
    (hC : (∫ y : ℝ, y ^ 0 ∂criticalInformationDepletedCarrier) + C =
      RHTower.normalizedPrimeArchMoment 0) :
    C < 0 := by
  linarith [normalizedPrimeArchMoment_zero_lt_integral_criticalInformationDepletedCarrier]

end RHTower.HedenmalmThetaSource

