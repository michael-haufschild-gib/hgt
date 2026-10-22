import GaloisForLFunctions.HTGeometry.PowerMomentSupport
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCalibratedPowerReciprocalMomentLaw

/-!
# Degree-two law for the calibrated power-reciprocal theta carrier

The source-selected power-reciprocal exponent is forced beyond `4` by the
first charged theta atom together with the source first-moment budget.
Consequently the calibrated carrier is supported in `(0, 1/81)`.

The quadratic moment of every calibrated power carrier is also identified
exactly with the normalized negative-power profile at twice the exponent.
This turns the next Cassini moment condition into one explicit scalar
source-profile identity.
-/

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

noncomputable section

/-- Raising a negative-power kernel to a natural power multiplies its
exponent by that power. -/
theorem negativePowerKernel_pow (alpha t : ℝ) (n : ℕ) :
    negativePowerKernel alpha t ^ n =
      negativePowerKernel ((n : ℝ) * alpha) t := by
  unfold negativePowerKernel
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Squaring a negative-power kernel doubles its exponent. -/
theorem negativePowerKernel_sq (alpha t : ℝ) :
    negativePowerKernel alpha t ^ 2 =
      negativePowerKernel (2 * alpha) t := by
  simpa using negativePowerKernel_pow alpha t 2

/-- Every natural power moment of the calibrated carrier is the source
mass times the normalized profile at the correspondingly multiplied
exponent. -/
theorem integral_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_pow
    (alpha : ℝ) (n : ℕ) :
    (∫ x : ℝ, x ^ n
        ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure alpha) =
      normalizedPrimeArchMoment 0 *
        thetaCuspNormalizedNegativePowerProfile ((n : ℝ) * alpha) := by
  let nu : Measure ℝ :=
    thetaCuspHigherLikelihoodTiltedMeasure (thetaCuspLikelihoodCoordinate 0)
  letI : IsFiniteMeasure nu :=
    thetaCuspHigherLikelihoodTiltedMeasure_finite
      (thetaCuspLikelihoodCoordinate_pos le_rfl)
  rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure,
    integral_smul_measure, smul_eq_mul,
    thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure]
  rw [integral_map
    (μ := thetaCuspHigherLikelihoodTiltedMeasure (thetaCuspLikelihoodCoordinate 0))
    (φ := negativePowerKernel alpha) (f := fun x : ℝ => x ^ n)
    (measurable_negativePowerKernel alpha).aemeasurable
    (continuous_id.pow n).aestronglyMeasurable]
  simp only [negativePowerKernel_pow]
  rw [thetaCuspCassiniPowerReciprocalCalibration,
    ENNReal.toReal_div,
    ENNReal.toReal_ofReal normalizedPrimeArchMoment_zero_pos.le]
  unfold thetaCuspNormalizedNegativePowerProfile
    normalizedNegativePowerProfile
  rw [Measure.real_def]
  ring

/-- Quadratic moment of the calibrated carrier is the source mass times
the normalized profile at twice the exponent. -/
theorem integral_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_sq
    (alpha : ℝ) :
    (∫ x : ℝ, x ^ 2
        ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure alpha) =
      normalizedPrimeArchMoment 0 *
        thetaCuspNormalizedNegativePowerProfile (2 * alpha) := by
  simpa using
    integral_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_pow
      alpha 2

private theorem thetaCuspHigherLikelihoodTiltedMeasure_seam_real_univ_le :
    (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)).real Set.univ ≤
        (8 / 2997 : ℝ) := by
  have h :=
    thetaCuspCassiniHigherReciprocalLikelihoodMeasure_measureReal_univ_le
  rw [thetaCuspCassiniHigherReciprocalLikelihoodMeasure, Measure.real_def,
    Measure.map_apply measurable_thetaCuspLikelihoodReciprocalGap
      MeasurableSet.univ] at h
  rw [Measure.real_def]
  simpa only [preimage_univ] using h

/-- The first charged theta atom keeps the fourth negative-power profile
strictly above the rational source first-moment ratio ceiling. -/
theorem nine_div_twoThousand_lt_thetaCuspNormalizedNegativePowerProfile_four :
    (9 / 2000 : ℝ) <
      thetaCuspNormalizedNegativePowerProfile 4 := by
  let nu : Measure ℝ :=
    thetaCuspHigherLikelihoodTiltedMeasure (thetaCuspLikelihoodCoordinate 0)
  letI : IsFiniteMeasure nu :=
    thetaCuspHigherLikelihoodTiltedMeasure_finite
      (thetaCuspLikelihoodCoordinate_pos le_rfl)
  have hmassENN : 0 < nu Set.univ := by
    simpa only [nu] using
      thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos
  have hmass : 0 < nu.real Set.univ :=
    ENNReal.toReal_pos hmassENN.ne' (measure_ne_top nu Set.univ)
  have hmassLe : nu.real Set.univ ≤ (8 / 2997 : ℝ) := by
    simpa only [nu] using
      thetaCuspHigherLikelihoodTiltedMeasure_seam_real_univ_le
  have hatom : (1 / 864 : ℝ) < nu.real {3} := by
    simpa only [nu] using
      one_div_eightHundredSixtyFour_lt_thetaCuspHigherLikelihoodTiltedMeasure_singleton_three_real
  have hsupport : ∀ᵐ t ∂nu, (3 : ℝ) ≤ t := by
    simpa only [nu] using
      ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0)
  have hint : Integrable (negativePowerKernel 4) nu :=
    integrable_negativePowerKernel_of_ae_lower_bound (c := 3)
      (by norm_num) hsupport (by norm_num)
  have hpow : (3 : ℝ) ^ (-(4 : ℝ)) = 1 / 81 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  have hsingle :
      ∫ t : ℝ in ({3} : Set ℝ), negativePowerKernel 4 t ∂nu =
        (1 / 81 : ℝ) * nu.real {3} := by
    rw [integral_singleton, smul_eq_mul,
      negativePowerKernel_eq_rpow (by norm_num : (0 : ℝ) < 3),
      hpow]
    ring
  have hle :
      ∫ t : ℝ in ({3} : Set ℝ), negativePowerKernel 4 t ∂nu ≤
        ∫ t : ℝ, negativePowerKernel 4 t ∂nu :=
    setIntegral_le_integral hint
      (Eventually.of_forall fun t => (negativePowerKernel_pos 4 t).le)
  unfold thetaCuspNormalizedNegativePowerProfile
    normalizedNegativePowerProfile
  apply (lt_div_iff₀ hmass).2
  calc
    (9 / 2000 : ℝ) * nu.real Set.univ ≤
        (9 / 2000 : ℝ) * (8 / 2997) :=
      mul_le_mul_of_nonneg_left hmassLe (by norm_num)
    _ < (1 / 81 : ℝ) * (1 / 864) := by norm_num
    _ < (1 / 81 : ℝ) * nu.real {3} :=
      mul_lt_mul_of_pos_left hatom (by norm_num)
    _ = ∫ t : ℝ in ({3} : Set ℝ), negativePowerKernel 4 t ∂nu :=
      hsingle.symm
    _ ≤ ∫ t : ℝ, negativePowerKernel 4 t ∂nu := hle

/-- Source first-to-zero moment ratio lies below `9/2000`. -/
theorem normalizedPrimeArchMoment_ratio_lt_nine_div_twoThousand :
    normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 <
      (9 / 2000 : ℝ) := by
  apply (div_lt_iff₀ normalizedPrimeArchMoment_zero_pos).2
  nlinarith [one_div_twentyFive_lt_normalizedPrimeArchMoment_zero,
    normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand]

/-- Source data force the unique barycenter-calibrating exponent past `4`. -/
theorem thetaCuspSourceSelectedPowerReciprocalExponent_gt_four :
    4 < thetaCuspSourceSelectedPowerReciprocalExponent := by
  let alpha := thetaCuspSourceSelectedPowerReciprocalExponent
  have hprofile :
      thetaCuspNormalizedNegativePowerProfile alpha <
        thetaCuspNormalizedNegativePowerProfile 4 := by
    rw [show thetaCuspNormalizedNegativePowerProfile alpha =
      normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 by
        exact thetaCuspSourceSelectedPowerReciprocalExponent_profile]
    exact normalizedPrimeArchMoment_ratio_lt_nine_div_twoThousand.trans
      nine_div_twoThousand_lt_thetaCuspNormalizedNegativePowerProfile_four
  by_contra h
  have halphaLe : alpha ≤ 4 := le_of_not_gt h
  rcases halphaLe.eq_or_lt with halphaEq | halphaLt
  · rw [halphaEq] at hprofile
    exact hprofile.false
  · have hstrict := strictAntiOn_thetaCuspNormalizedNegativePowerProfile
    have hfourMem : (4 : ℝ) ∈ Set.Ici 0 := by norm_num
    have halphaMem : alpha ∈ Set.Ici 0 := by
      exact le_trans (by norm_num)
        thetaCuspSourceSelectedPowerReciprocalExponent_gt_one.le
    have hopposite := hstrict halphaMem hfourMem halphaLt
    exact (not_lt_of_ge hopposite.le) hprofile

/-- The source-selected carrier is concentrated strictly inside
`(0, 1/81)`. -/
theorem ae_thetaCuspSourceSelectedPowerReciprocal_support_one_div_eightyOne :
    ∀ᵐ x
      ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
        thetaCuspSourceSelectedPowerReciprocalExponent,
      0 < x ∧ x < 1 / 81 := by
  let alpha := thetaCuspSourceSelectedPowerReciprocalExponent
  rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure]
  apply Measure.ae_smul_measure
  rw [thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure]
  apply (ae_map_iff (measurable_negativePowerKernel alpha).aemeasurable
    (measurableSet_Ioi.inter measurableSet_Iio)).2
  filter_upwards [
    ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)] with t ht
  constructor
  · exact negativePowerKernel_pos alpha t
  · rw [negativePowerKernel_eq_rpow
      (zero_lt_one.trans (by linarith : 1 < t))]
    have hbase : t ^ (-alpha) ≤ (3 : ℝ) ^ (-alpha) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) ht
        (by
          have h := thetaCuspSourceSelectedPowerReciprocalExponent_gt_four
          apply neg_nonpos.mpr
          exact le_trans (by norm_num : (0 : ℝ) ≤ 4)
            (by simpa only [alpha] using h.le))
    have hexponent : (3 : ℝ) ^ (-alpha) < (3 : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        (neg_lt_neg
          (by
            simpa only [alpha] using
              thetaCuspSourceSelectedPowerReciprocalExponent_gt_four))
    have hpow : (3 : ℝ) ^ (-(4 : ℝ)) = 1 / 81 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rw [hpow] at hexponent
    exact hbase.trans_lt hexponent

/-- Every adjacent pair of source-selected carrier moments satisfies the
same strict support contraction. -/
theorem thetaCuspSourceSelectedPowerReciprocal_moment_succ_lt
    (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 1)
        ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
          thetaCuspSourceSelectedPowerReciprocalExponent) <
      (1 / 81 : ℝ) *
        ∫ x : ℝ, x ^ n
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent := by
  let mu : Measure ℝ :=
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
      thetaCuspSourceSelectedPowerReciprocalExponent
  letI : IsFiniteMeasure mu :=
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_finite _
  have hmu : 0 < mu Set.univ := by
    dsimp only [mu]
    rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_univ]
    exact ENNReal.ofReal_pos.mpr normalizedPrimeArchMoment_zero_pos
  letI : NeZero mu := ⟨by
    intro hzero
    rw [hzero] at hmu
    simp at hmu⟩
  have hsupport : ∀ᵐ x ∂mu, 0 < x ∧ x < 1 / 81 := by
    simpa only [mu] using
      ae_thetaCuspSourceSelectedPowerReciprocal_support_one_div_eightyOne
  have hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu := by
    intro k
    refine Integrable.of_bound
      (continuous_id.pow k).aestronglyMeasurable 1 ?_
    filter_upwards [hsupport] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1.le k)]
    exact pow_le_one₀ hx.1.le (hx.2.le.trans (by norm_num))
  simpa only [mu] using
    HTGeometry.integral_pow_succ_lt_upper_mul_integral_pow_of_ae_pos_lt
      (mu := mu) (f := fun x : ℝ => x) (R := (1 / 81 : ℝ)) n
      (hint n) (hint (n + 1)) hsupport

/-- Exact degree-two value at the source-selected exponent. -/
theorem thetaCuspSourceSelectedPowerReciprocal_secondMoment :
    (∫ x : ℝ, x ^ 2
        ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
          thetaCuspSourceSelectedPowerReciprocalExponent) =
      normalizedPrimeArchMoment 0 *
        thetaCuspNormalizedNegativePowerProfile
          (2 * thetaCuspSourceSelectedPowerReciprocalExponent) :=
  integral_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_sq _

/-- The selected carrier's quadratic moment is strictly below one
eighty-first of its source-matched first moment. -/
theorem thetaCuspSourceSelectedPowerReciprocal_secondMoment_lt_one_div_eightyOne_mul_first :
    (∫ x : ℝ, x ^ 2
        ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
          thetaCuspSourceSelectedPowerReciprocalExponent) <
      (1 / 81 : ℝ) * normalizedPrimeArchMoment 1 := by
  have hstrict :=
    thetaCuspSourceSelectedPowerReciprocal_moment_succ_lt 1
  have hfirst :=
    thetaCuspSourceSelectedPowerReciprocal_mass_and_firstMoment.2
  simpa [hfirst] using hstrict

/-- Matching two adjacent source moments with the selected carrier
forces the same strict `1/81` contraction on that source pair. -/
theorem normalizedPrimeArchMoment_succ_lt_one_div_eightyOne_mul_of_selectedPowerReciprocal_matches
    (n : ℕ)
    (hn :
      (∫ x : ℝ, x ^ n
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent) =
        normalizedPrimeArchMoment n)
    (hsucc :
      (∫ x : ℝ, x ^ (n + 1)
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent) =
        normalizedPrimeArchMoment (n + 1)) :
    normalizedPrimeArchMoment (n + 1) <
      (1 / 81 : ℝ) * normalizedPrimeArchMoment n := by
  rw [← hsucc, ← hn]
  exact thetaCuspSourceSelectedPowerReciprocal_moment_succ_lt n

/-- Exact degree-two matching would force a strict source moment-ratio
constraint. -/
theorem normalizedPrimeArchMoment_two_lt_one_div_eightyOne_mul_one_of_selectedPowerReciprocal_match
    (hmatch :
      (∫ x : ℝ, x ^ 2
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent) =
        normalizedPrimeArchMoment 2) :
    normalizedPrimeArchMoment 2 <
      (1 / 81 : ℝ) * normalizedPrimeArchMoment 1 := by
  exact
    normalizedPrimeArchMoment_succ_lt_one_div_eightyOne_mul_of_selectedPowerReciprocal_matches
      1 (by
        simpa using
          thetaCuspSourceSelectedPowerReciprocal_mass_and_firstMoment.2)
      (by simpa using hmatch)

end

end RHTower
