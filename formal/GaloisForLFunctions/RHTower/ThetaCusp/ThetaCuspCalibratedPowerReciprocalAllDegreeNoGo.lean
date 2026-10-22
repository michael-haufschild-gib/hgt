import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCalibratedPowerReciprocalSecondMomentLaw
import GaloisForLFunctions.RHTower.PrimeArchContinuousThetaReporterNoGo

/-!
# All-degree no-go for the calibrated power-reciprocal theta carrier

The source-selected power carrier matches the canonical zeroth and first moments and survives its
degree-two ratio gate.  It nevertheless cannot match the complete prime--archimedean moment tower.

The first higher theta spectral summand contains a positive Lebesgue ray on `(3, infinity)`.  Its
strictly positive Gibbs tilt therefore has full open-set support there.  The selected negative-power
reporter is continuous and nonconstant, so its pushforward places positive mass outside the closed
countable Xi thermal-node set.  Unrestricted moment rigidity would identify any all-degree witness
with the canonical atomic Xi measure, which is carried by exactly that countable set.  This gives an
unconditional contradiction and forces any successor producer to quantize the source before moment
matching.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- The positive Lebesgue ray in the first higher theta spectral summand makes restricted volume
on `(3, infinity)` absolutely continuous with respect to the complete higher spectral measure. -/
theorem volume_restrict_Ioi_three_absolutelyContinuous_thetaCuspHigherLikelihoodSpectralMeasure :
    (volume.restrict (Ioi 3) : Measure ℝ) ≪
      thetaCuspHigherLikelihoodSpectralMeasure := by
  intro s htotal
  let ray : Measure ℝ :=
    ENNReal.ofReal (thetaCuspLikelihoodRayWeight 2) •
      volume.restrict (Ioi (thetaCuspLikelihoodGap 2))
  have hrayLeAtom : ray ≤ thetaCuspAtomLikelihoodSpectralMeasure 2 := by
    unfold ray thetaCuspAtomLikelihoodSpectralMeasure
    exact Measure.le_add_left (le_refl _)
  have hatomLeTotal :
      thetaCuspAtomLikelihoodSpectralMeasure 2 ≤
        thetaCuspHigherLikelihoodSpectralMeasure := by
    unfold thetaCuspHigherLikelihoodSpectralMeasure
    simpa using
      (Measure.le_sum
        (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0)
  have hrayZero : ray s = 0 := by
    apply bot_unique
    have hle := (hrayLeAtom.trans hatomLeTotal) s
    rw [htotal] at hle
    exact hle
  unfold ray at hrayZero
  rw [Measure.smul_apply, smul_eq_mul,
    show thetaCuspLikelihoodGap 2 = 3 by norm_num [thetaCuspLikelihoodGap]] at hrayZero
  exact (mul_eq_zero.mp hrayZero).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr
      (thetaCuspLikelihoodRayWeight_pos (n := 2) (by norm_num))))

/-- A strictly positive Gibbs density preserves absolute continuity in the reverse direction
needed to retain the open ray. -/
theorem thetaCuspHigherLikelihoodSpectralMeasure_absolutelyContinuous_tilted (B : ℝ) :
    thetaCuspHigherLikelihoodSpectralMeasure ≪
      thetaCuspHigherLikelihoodTiltedMeasure B := by
  unfold thetaCuspHigherLikelihoodTiltedMeasure
  apply withDensity_absolutelyContinuous'
  · exact (measurable_thetaCuspHigherLikelihoodTiltDensity B).coe_nnreal_ennreal.aemeasurable
  · filter_upwards with t
    simp [thetaCuspHigherLikelihoodTiltDensity,
      Real.toNNReal_eq_zero, not_le, Real.exp_pos]

/-- Restricted volume on the first ray is absolutely continuous with respect to every tilted
higher likelihood measure. -/
theorem volume_restrict_Ioi_three_absolutelyContinuous_thetaCuspHigherLikelihoodTiltedMeasure
    (B : ℝ) :
    (volume.restrict (Ioi 3) : Measure ℝ) ≪
      thetaCuspHigherLikelihoodTiltedMeasure B :=
  volume_restrict_Ioi_three_absolutelyContinuous_thetaCuspHigherLikelihoodSpectralMeasure.trans
    (thetaCuspHigherLikelihoodSpectralMeasure_absolutelyContinuous_tilted B)

/-- Every open set meeting the interior of the first theta ray has positive tilted source mass. -/
theorem thetaCuspHigherLikelihoodTiltedMeasure_pos_of_isOpen_inter_Ioi_three_nonempty
    {B : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hne : (U ∩ Ioi 3).Nonempty) :
    0 < thetaCuspHigherLikelihoodTiltedMeasure B U := by
  have hvol : 0 < volume (U ∩ Ioi 3) :=
    (hU.inter isOpen_Ioi).measure_pos volume hne
  have hbase : 0 < (volume.restrict (Ioi 3) : Measure ℝ) U := by
    rw [Measure.restrict_apply hU.measurableSet]
    exact hvol
  apply lt_of_not_ge
  intro hle
  have hzero : thetaCuspHigherLikelihoodTiltedMeasure B U = 0 := bot_unique hle
  exact (ne_of_gt hbase)
    (volume_restrict_Ioi_three_absolutelyContinuous_thetaCuspHigherLikelihoodTiltedMeasure B hzero)

/-- A positive negative-power exponent separates the two explicit interior source points. -/
theorem negativePowerKernel_four_ne_five
    {alpha : ℝ} (halpha : 0 < alpha) :
    negativePowerKernel alpha 4 ≠ negativePowerKernel alpha 5 := by
  rw [negativePowerKernel_eq_rpow (by norm_num),
    negativePowerKernel_eq_rpow (by norm_num)]
  exact ne_of_gt
    (Real.strictAntiOn_rpow_Ioi_of_exponent_neg (neg_neg_of_pos halpha)
      (by norm_num) (by norm_num) (by norm_num))

/-- The selected continuous power reporter cannot map the connected first ray into the countable
Xi thermal carrier. -/
theorem not_selectedPowerReciprocal_image_Ioi_three_subset_xiThermalCompactNodeSet :
    ¬ negativePowerKernel thetaCuspSourceSelectedPowerReciprocalExponent '' Ioi 3 ⊆
      xiThermalCompactNodeSet := by
  intro hsub
  have hsingle :
      (negativePowerKernel thetaCuspSourceSelectedPowerReciprocalExponent '' Ioi 3).Subsingleton :=
    countable_isPreconnected_subsingleton_real
      (xiThermalCompactNodeSet_countable.mono hsub)
      (isPreconnected_Ioi.image _
        (by
          unfold negativePowerKernel
          have hlog : ContinuousOn Real.log (Ioi (3 : ℝ)) :=
            Real.continuousOn_log.mono fun t ht =>
              ne_of_gt (lt_trans (by norm_num) ht)
          have hinner : ContinuousOn
              (fun t : ℝ =>
                -thetaCuspSourceSelectedPowerReciprocalExponent * Real.log t)
              (Ioi (3 : ℝ)) :=
            continuousOn_const.mul hlog
          exact Real.continuous_exp.continuousOn.comp hinner
            (fun _ _ => Set.mem_univ _)))
  have heq := hsingle ⟨4, by norm_num, rfl⟩ ⟨5, by norm_num, rfl⟩
  exact negativePowerKernel_four_ne_five
    (lt_trans (by norm_num) thetaCuspSourceSelectedPowerReciprocalExponent_gt_one) heq

/-- Mass calibration of the selected power pushforward is strictly positive. -/
theorem thetaCuspCassiniPowerReciprocalCalibration_pos :
    0 < thetaCuspCassiniPowerReciprocalCalibration := by
  unfold thetaCuspCassiniPowerReciprocalCalibration
  apply ENNReal.div_pos
  · exact (ENNReal.ofReal_pos.mpr normalizedPrimeArchMoment_zero_pos).ne'
  · letI : IsFiniteMeasure
        (thetaCuspHigherLikelihoodTiltedMeasure (thetaCuspLikelihoodCoordinate 0)) :=
      thetaCuspHigherLikelihoodTiltedMeasure_finite
        (thetaCuspLikelihoodCoordinate_pos le_rfl)
    exact measure_ne_top _ _

/-- The selected calibrated carrier has positive mass away from the closed countable Xi thermal
node set.  This is the exact source-side obstruction to complete moment matching. -/
theorem thetaCuspSourceSelectedPowerReciprocal_compl_xiThermalCompactNodeSet_pos :
    0 < thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
        thetaCuspSourceSelectedPowerReciprocalExponent
          xiThermalCompactNodeSetᶜ := by
  let alpha := thetaCuspSourceSelectedPowerReciprocalExponent
  let node : ℝ → ℝ := negativePowerKernel alpha
  have hcont : ContinuousOn node (Ioi (3 : ℝ)) := by
    dsimp only [node]
    unfold negativePowerKernel
    have hlog : ContinuousOn Real.log (Ioi (3 : ℝ)) :=
      Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (lt_trans (by norm_num) ht)
    have hinner : ContinuousOn
        (fun t : ℝ => -alpha * Real.log t) (Ioi (3 : ℝ)) :=
      continuousOn_const.mul hlog
    exact Real.continuous_exp.continuousOn.comp hinner
      (fun _ _ => Set.mem_univ _)
  have hnot : ¬ node '' Ioi (3 : ℝ) ⊆ xiThermalCompactNodeSet := by
    simpa only [node, alpha] using
      not_selectedPowerReciprocal_image_Ioi_three_subset_xiThermalCompactNodeSet
  obtain ⟨y, ⟨t, ht, rfl⟩, htK⟩ := Set.not_subset.mp hnot
  let U : Set ℝ := Ioi 3 ∩ node ⁻¹' xiThermalCompactNodeSetᶜ
  have hUopen : IsOpen U :=
    hcont.isOpen_inter_preimage isOpen_Ioi
      xiThermalCompactNodeSet_isClosed.isOpen_compl
  have htU : t ∈ U := ⟨ht, htK⟩
  have hsource :
      0 < thetaCuspHigherLikelihoodTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0) U :=
    thetaCuspHigherLikelihoodTiltedMeasure_pos_of_isOpen_inter_Ioi_three_nonempty
      hUopen ⟨t, htU, ht⟩
  have hpreimage :
      0 < thetaCuspHigherLikelihoodTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0)
          (node ⁻¹' xiThermalCompactNodeSetᶜ) :=
    hsource.trans_le (measure_mono inter_subset_right)
  rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure,
    Measure.smul_apply, smul_eq_mul,
    thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure,
    Measure.map_apply (measurable_negativePowerKernel alpha)
      xiThermalCompactNodeSet_isClosed.isOpen_compl.measurableSet]
  exact ENNReal.mul_pos thetaCuspCassiniPowerReciprocalCalibration_pos.ne' hpreimage.ne'

/-- Every power is integrable against the source-selected compact power carrier. -/
theorem integrable_pow_thetaCuspSourceSelectedPowerReciprocal (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n)
      (thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
        thetaCuspSourceSelectedPowerReciprocalExponent) := by
  let mu : Measure ℝ :=
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
      thetaCuspSourceSelectedPowerReciprocalExponent
  letI : IsFiniteMeasure mu :=
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_finite _
  have hsupport : ∀ᵐ x ∂mu, 0 < x ∧ x < 1 / 81 := by
    simpa only [mu] using
      ae_thetaCuspSourceSelectedPowerReciprocal_support_one_div_eightyOne
  refine Integrable.of_bound (continuous_id.pow n).aestronglyMeasurable 1 ?_
  filter_upwards [hsupport] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1.le n)]
  exact pow_le_one₀ hx.1.le (hx.2.le.trans (by norm_num))

/-- **Route-Q all-degree no-go.** The unique power-reciprocal theta carrier selected by source mass
and barycenter cannot represent the complete normalized prime--archimedean moment tower. -/
theorem not_all_degree_thetaCuspSourceSelectedPowerReciprocal_moment_matching :
    ¬ ∀ k : ℕ,
      normalizedPrimeArchMoment k =
        ∫ x : ℝ, x ^ k
          ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
            thetaCuspSourceSelectedPowerReciprocalExponent := by
  intro hmatch
  let mu : Measure ℝ :=
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
      thetaCuspSourceSelectedPowerReciprocalExponent
  have hwitness : IsPrimeArchMomentWitness mu := by
    exact ⟨fun k => by simpa only [mu] using hmatch k,
      fun k => by
        simpa only [mu] using integrable_pow_thetaCuspSourceSelectedPowerReciprocal k⟩
  have heq : mu = primeArchXiCompactMomentMeasure :=
    hwitness.eq_primeArchXiCompactMomentMeasure
  have hpos : 0 < mu xiThermalCompactNodeSetᶜ := by
    simpa only [mu] using
      thetaCuspSourceSelectedPowerReciprocal_compl_xiThermalCompactNodeSet_pos
  rw [heq, primeArchXiCompactMomentMeasure_compl_xiThermalCompactNodeSet_eq_zero] at hpos
  exact hpos.false

end

end RHTower
