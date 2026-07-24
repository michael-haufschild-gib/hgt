import GaloisForLFunctions.RHTower.ThetaCuspCassiniMarkovBoundaryTransport
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentFloor

/-!
# First-moment obstruction to the calibrated reciprocal-gap carrier

The source-normalized Cassini reciprocal carrier has the correct zeroth moment by construction.
It nevertheless cannot represent the positive-degree prime--archimedean moments.  The first
higher square gap forces an atom at reciprocal coordinate `1/3`.  Source domination bounds the
total higher-tail mass, so calibration gives this atom a fixed positive fraction of the completed
mass.  Its contribution alone makes the candidate first moment larger than the actual source first
moment.
-/

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

noncomputable section

/-- The zeroth normalized prime--archimedean moment has a source-only rational floor. -/
theorem one_div_twentyFive_lt_normalizedPrimeArchMoment_zero :
    (1 / 25 : ℝ) < normalizedPrimeArchMoment 0 := by
  have hM0 := normalizedPrimeArchMoment_zero_pos
  have hM1 := normalizedPrimeArchMoment_one_pos
  have hmu2 :=
    twoHundredSixtyNine_div_fiftyThousand_lt_thetaCuspNormalizedEvenMoment_two
  have heq := normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment
  rw [← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment] at heq
  by_contra h
  have hM0upper : normalizedPrimeArchMoment 0 ≤ 1 / 25 := le_of_not_gt h
  nlinarith [sq_nonneg (normalizedPrimeArchMoment 0 - 1 / 25)]

/-- Cubing the existing first-theta-exponential floor gives a lower bound at the first higher
square gap. -/
theorem twentySeven_div_threeHundredFortyThreeThousand_lt_exp_neg_three_pi :
    (27 / 343000 : ℝ) < Real.exp (-3 * Real.pi) := by
  have h := three_div_seventy_lt_exp_neg_pi
  have hcube : (3 / 70 : ℝ) ^ 3 < Real.exp (-Real.pi) ^ 3 :=
    pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at hcube
  convert hcube using 1 <;> norm_num

/-- The tilted higher likelihood measure has exact first-atom mass `16 exp(-3 pi)` at gap `3`. -/
theorem thetaCuspHigherLikelihoodTiltedMeasure_seam_singleton_three :
    thetaCuspHigherLikelihoodTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0) {3} =
      ENNReal.ofReal (16 * Real.exp (-3 * Real.pi)) := by
  have h := thetaCuspLikelihoodSeamTiltedMeasure_singleton_three
    (thetaCuspLikelihoodCoordinate 0)
  rw [thetaCuspLikelihoodSeamTiltedMeasure, Measure.add_apply] at h
  have hdirac : Measure.dirac (0 : ℝ) {3} = 0 := by simp
  rw [hdirac, zero_add] at h
  rw [h]
  rw [thetaCuspHigherLikelihoodTiltDensity]
  rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ (Real.exp_pos _).le]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply congrArg ENNReal.ofReal
  rw [thetaCuspLikelihoodCoordinate, thetaCuspLikelihoodAtomWeight,
    thetaCuspLikelihoodGap]
  norm_num
  calc
    Real.exp ((3 / 2 - Real.pi) * 3) *
        (Real.exp (-(9 / 2)) * 16) =
      16 * (Real.exp ((3 / 2 - Real.pi) * 3) *
        Real.exp (-(9 / 2))) := by ring
    _ = 16 * Real.exp (-3 * Real.pi) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = 16 * Real.exp (-(3 * Real.pi)) := by
      congr 2
      ring

/-- Reciprocal pushforward sends the forced gap-`3` atom exactly to `1/3`. -/
theorem thetaCuspCassiniHigherReciprocalLikelihoodMeasure_singleton_oneThird :
    thetaCuspCassiniHigherReciprocalLikelihoodMeasure {(1 / 3 : ℝ)} =
      ENNReal.ofReal (16 * Real.exp (-3 * Real.pi)) := by
  rw [thetaCuspCassiniHigherReciprocalLikelihoodMeasure,
    Measure.map_apply measurable_thetaCuspLikelihoodReciprocalGap
      (measurableSet_singleton (1 / 3 : ℝ))]
  have hpre :
      thetaCuspLikelihoodReciprocalGap ⁻¹' {(1 / 3 : ℝ)} = ({3} : Set ℝ) := by
    ext r
    simp only [mem_preimage, mem_singleton_iff]
    rw [thetaCuspLikelihoodReciprocalGap]
    constructor
    · intro h
      have hne : r ≠ 0 := by
        intro hr
        subst r
        norm_num at h
      field_simp [hne] at h
      linarith
    · rintro rfl
      norm_num
  rw [hpre, thetaCuspHigherLikelihoodTiltedMeasure_seam_singleton_three]

/-- Total uncalibrated reciprocal mass is controlled by the existing source atom-domination
weight. -/
theorem thetaCuspCassiniHigherReciprocalLikelihoodMeasure_measureReal_univ_le :
    thetaCuspCassiniHigherReciprocalLikelihoodMeasure.real Set.univ ≤
      (8 / 2997 : ℝ) := by
  have hB : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos le_rfl
  have hfirst : 0 < thetaCuspSourceTerm 0 1 :=
    thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hB
  have htail := thetaCuspFullSource_sub_first_le (x := 0) le_rfl
  have hratio :
      thetaCuspHigherToFirstAtomLikelihoodRatio 0 ≤
        thetaCuspHigherAtomDominationWeight := by
    rw [thetaCuspHigherToFirstAtomLikelihoodRatio]
    exact (div_le_iff₀ hfirst).2 htail
  have hresponse :
      thetaCuspHigherLikelihoodSpectralResponse
          (thetaCuspLikelihoodCoordinate 0) ≤
        thetaCuspHigherAtomDominationWeight := by
    rw [thetaCuspHigherLikelihoodSpectralResponse_coordinate_of_coordinate_pos hB]
    exact hratio
  have hmoment :
      thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 0 ≤
        thetaCuspHigherAtomDominationWeight := by
    rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
    simp only [pow_zero, one_mul]
    rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB]
    exact hresponse
  have hmass :
      thetaCuspCassiniHigherReciprocalLikelihoodMeasure.real Set.univ =
        thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 0 := by
    rw [thetaCuspCassiniHigherReciprocalLikelihoodMeasure, Measure.real_def,
      Measure.map_apply measurable_thetaCuspLikelihoodReciprocalGap
        MeasurableSet.univ]
    simp only [preimage_univ]
    rw [thetaCuspHigherLikelihoodSpectralMoment]
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one, Measure.real_def]
  rw [hmass]
  exact hmoment.trans thetaCuspHigherAtomDominationWeight_le_geometric_rational

/-- Exact calibrated mass of the forced reciprocal atom. -/
theorem thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_singleton_oneThird :
    thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure.real
        {(1 / 3 : ℝ)} =
      normalizedPrimeArchMoment 0 /
          thetaCuspCassiniHigherReciprocalLikelihoodMeasure.real Set.univ *
        (16 * Real.exp (-3 * Real.pi)) := by
  rw [Measure.real_def,
    thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure,
    Measure.smul_apply, smul_eq_mul,
    thetaCuspCassiniHigherReciprocalCalibration,
    thetaCuspCassiniHigherReciprocalLikelihoodMeasure_singleton_oneThird,
    ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofReal normalizedPrimeArchMoment_zero_pos.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 16 * Real.exp (-3 * Real.pi))]
  rfl

/-- Calibration forces more than one percent of the total measure onto reciprocal gap `1/3`. -/
theorem one_div_hundred_lt_thetaCuspCassiniCalibratedReciprocal_atom :
    (1 / 100 : ℝ) <
      thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure.real
        {(1 / 3 : ℝ)} := by
  let mass : ℝ :=
    thetaCuspCassiniHigherReciprocalLikelihoodMeasure.real Set.univ
  let atom : ℝ := 16 * Real.exp (-3 * Real.pi)
  have hmeasurePos :
      0 < thetaCuspCassiniHigherReciprocalLikelihoodMeasure Set.univ := by
    rw [thetaCuspCassiniHigherReciprocalLikelihoodMeasure,
      Measure.map_apply measurable_thetaCuspLikelihoodReciprocalGap
        MeasurableSet.univ]
    simpa only [preimage_univ] using
      thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos
  have hmassPos : 0 < mass := by
    dsimp only [mass, Measure.real_def]
    exact ENNReal.toReal_pos
      hmeasurePos.ne'
      (by
        letI : IsFiniteMeasure thetaCuspCassiniHigherReciprocalLikelihoodMeasure :=
          thetaCuspCassiniHigherReciprocalLikelihoodMeasure_finite
        exact measure_ne_top
          thetaCuspCassiniHigherReciprocalLikelihoodMeasure Set.univ)
  have hmass : mass ≤ 8 / 2997 := by
    simpa only [mass] using
      thetaCuspCassiniHigherReciprocalLikelihoodMeasure_measureReal_univ_le
  have hM0 := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have hatom : (432 / 343000 : ℝ) < atom := by
    dsimp only [atom]
    nlinarith [twentySeven_div_threeHundredFortyThreeThousand_lt_exp_neg_three_pi]
  have hprod :
      (1 / 25 : ℝ) * (432 / 343000) <
        normalizedPrimeArchMoment 0 * atom := by
    calc
      (1 / 25 : ℝ) * (432 / 343000) <
          normalizedPrimeArchMoment 0 * (432 / 343000) :=
        mul_lt_mul_of_pos_right hM0 (by norm_num)
      _ < normalizedPrimeArchMoment 0 * atom :=
        mul_lt_mul_of_pos_left hatom normalizedPrimeArchMoment_zero_pos
  rw [thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_singleton_oneThird]
  change (1 / 100 : ℝ) <
    normalizedPrimeArchMoment 0 / mass * atom
  rw [show normalizedPrimeArchMoment 0 / mass * atom =
    (normalizedPrimeArchMoment 0 * atom) / mass by ring]
  apply (lt_div_iff₀ hmassPos).2
  calc
    (1 / 100 : ℝ) * mass ≤ (1 / 100 : ℝ) * (8 / 2997) :=
      mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ < (1 / 25 : ℝ) * (432 / 343000) := by norm_num
    _ < normalizedPrimeArchMoment 0 * atom := hprod

/-- The forced reciprocal atom alone puts the candidate first moment above `1/300`. -/
theorem one_div_threeHundred_lt_thetaCuspCassiniCalibratedReciprocal_firstMoment :
    (1 / 300 : ℝ) <
      ∫ x : ℝ, x ∂thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure := by
  let μ := thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure
  letI : IsFiniteMeasure μ :=
    thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_finite
  have hsupport : ∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ 1 / 3 :=
    ae_thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_support
  have hint : Integrable (fun x : ℝ => x) μ := by
    refine Integrable.of_bound continuous_id.aestronglyMeasurable (1 / 3) ?_
    filter_upwards [hsupport] with x hx
    simpa only [Real.norm_eq_abs] using hx.2
  have hsingle :
      ∫ x : ℝ in ({(1 / 3 : ℝ)} : Set ℝ), x ∂μ =
        (1 / 3 : ℝ) * μ.real {(1 / 3 : ℝ)} := by
    rw [integral_singleton, smul_eq_mul]
    ring
  have hle :
      ∫ x : ℝ in ({(1 / 3 : ℝ)} : Set ℝ), x ∂μ ≤
        ∫ x : ℝ, x ∂μ :=
    setIntegral_le_integral hint (hsupport.mono fun _ hx => hx.1)
  rw [hsingle] at hle
  have hatom :
      (1 / 100 : ℝ) < μ.real {(1 / 3 : ℝ)} := by
    simpa only [μ] using
      one_div_hundred_lt_thetaCuspCassiniCalibratedReciprocal_atom
  nlinarith

/-- The calibrated reciprocal carrier's first moment is strictly larger than the actual completed
source first moment. -/
theorem normalizedPrimeArchMoment_one_lt_thetaCuspCassiniCalibratedReciprocal_firstMoment :
    normalizedPrimeArchMoment 1 <
      ∫ x : ℝ, x ∂thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure := by
  have hsource := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  have hcand :=
    one_div_threeHundred_lt_thetaCuspCassiniCalibratedReciprocal_firstMoment
  nlinarith

/-- **Calibrated reciprocal-gap no-go.** Positive-degree moment matching fails already at degree
one. -/
theorem not_thetaCuspCassiniCalibratedReciprocalPositiveMomentMatching :
    ¬ ThetaCuspCassiniCalibratedReciprocalPositiveMomentMatching := by
  intro hmatch
  have hfirst := hmatch 1 (by norm_num)
  simp only [pow_one] at hfirst
  exact (ne_of_lt
    normalizedPrimeArchMoment_one_lt_thetaCuspCassiniCalibratedReciprocal_firstMoment)
    hfirst

end

end RHTower
