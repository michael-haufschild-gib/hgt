import GaloisForLFunctions.RHTower.HedenmalmQuantileBoundaryFlux
import GaloisForLFunctions.RHTower.HedenmalmSourceMoments
import GaloisForLFunctions.RHTower.HedenmalmThetaResolventLogJet

/-!
# Boundary-null geometry of the theta quantile source

The phase-sensitive quantile source has zero monopole.  Consequently its incoming and outgoing
rank-two boundary amplitudes are exact negatives, and its boundary flux vanishes.  Thus the
canonical logarithmic-jet source starts on the non-coercive light cone of the mixed-inertia Green
form: the raw Green identity cannot control its resolvent row without tracking the second boundary
channel.
-/

open Complex MeasureTheory Set

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmClosedWeightedDerivative
  GaloisForLFunctions.HTGeometry

/-! ### Port reconstruction -/

/-- Monopole is the symmetric sum of incoming and outgoing boundary ports. -/
theorem pinnedMean_eq_in_add_out_div_sqrtTwo (g : H) :
    pinnedMean g =
      (pinnedInAmplitude g + pinnedOutAmplitude g) /
        ((Real.sqrt 2 : ℝ) : ℂ) := by
  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ^ (2 : ℕ) = (2 : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [pinnedInAmplitude, pinnedOutAmplitude]
  field_simp
  linear_combination (pinnedMean g) * hsqrt

/-- Centered dipole is the antisymmetric difference of boundary ports. -/
theorem pinnedCentered_eq_out_sub_in_div_sqrtTwo (g : H) :
    pinnedCentered g =
      (pinnedOutAmplitude g - pinnedInAmplitude g) /
        ((Real.sqrt 2 : ℝ) : ℂ) := by
  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ^ (2 : ℕ) = (2 : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [pinnedInAmplitude, pinnedOutAmplitude]
  field_simp
  linear_combination (pinnedCentered g) * hsqrt

/-- The canonical theta quantile source has zero pinned monopole. -/
theorem pinnedMean_thetaQuantileCoordinate_eq_zero :
    pinnedMean thetaQuantileCoordinate = 0 := by
  rw [pinnedMean, integral_congr_ae thetaQuantileCoordinate_ae,
    integral_complex_ofReal, unitIntervalMeasure_eq, integral_quantileFun]
  norm_num

/-! ### Strict dipole charge -/

/-- Even theta source has median zero. -/
theorem thetaSource_cdfFun_zero :
    thetaSource.cdfFun 0 = 1 / 2 := by
  have h := HedenmalmIntervalAnomaly.cdfFun_neg thetaSource thetaSource_even 0
  norm_num at h ⊢
  linarith

/-- Quantile vanishes exactly at the median coordinate. -/
theorem thetaSource_quantileFun_half :
    thetaSource.quantileFun (1 / 2) = 0 := by
  rw [← thetaSource_cdfFun_zero, thetaSource.quantile_cdfFun]

/-- Quantile and centered coordinate have the same strict sign away from the median. -/
theorem sub_half_mul_thetaSource_quantileFun_pos {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hne : t ≠ 1 / 2) :
    0 < (t - 1 / 2) * thetaSource.quantileFun t := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hq := thetaSource.strictMonoOn_quantileFun ht hhalf hlt
    rw [thetaSource_quantileFun_half] at hq
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt) hq
  · have hq := thetaSource.strictMonoOn_quantileFun hhalf ht hgt
    rw [thetaSource_quantileFun_half] at hq
    exact mul_pos (sub_pos.mpr hgt) hq

/-- Centered quantile product is integrable on the unit interval. -/
theorem integrableOn_sub_half_mul_thetaSource_quantileFun :
    IntegrableOn
      (fun t : ℝ => (t - 1 / 2) * thetaSource.quantileFun t)
      (Ioo (0 : ℝ) 1) volume := by
  refine integrableOn_quantileFun_thetaSource.bdd_mul (c := 1)
    ((continuous_id.sub continuous_const).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [ht.1, ht.2]

/-- Strict monotonicity makes theta quantile's centered dipole integral positive. -/
theorem integral_sub_half_mul_thetaSource_quantileFun_pos :
    0 < ∫ t in Ioo (0 : ℝ) 1,
      (t - 1 / 2) * thetaSource.quantileFun t := by
  let g : ℝ → ℝ := fun t => (t - 1 / 2) * thetaSource.quantileFun t
  have hgint : IntegrableOn g (Ioo (0 : ℝ) 1) volume :=
    integrableOn_sub_half_mul_thetaSource_quantileFun
  have hgnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    by_cases h : t = 1 / 2
    · simp [g, h]
    · exact (sub_half_mul_thetaSource_quantileFun_pos ht h).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hgnn hgint).2
  have hsubset : Ioo (3 / 4 : ℝ) (7 / 8) ⊆
      Function.support g ∩ Ioo (0 : ℝ) 1 := by
    intro t ht
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have htne : t ≠ (1 / 2 : ℝ) := by linarith [ht.1]
    exact ⟨ne_of_gt (sub_half_mul_thetaSource_quantileFun_pos ht01 htne), ht01⟩
  have hvolume : 0 < volume (Ioo (3 / 4 : ℝ) (7 / 8)) := by
    rw [Real.volume_Ioo]
    norm_num
  exact hvolume.trans_le (measure_mono hsubset)

/-- Ordinary first quantile moment equals centered dipole because quantile monopole vanishes. -/
theorem integral_mul_thetaSource_quantileFun_pos :
    0 < ∫ t in Ioo (0 : ℝ) 1, t * thetaSource.quantileFun t := by
  have hqint := integrableOn_quantileFun_thetaSource
  have hcint := integrableOn_sub_half_mul_thetaSource_quantileFun
  calc
    0 < ∫ t in Ioo (0 : ℝ) 1,
        (t - 1 / 2) * thetaSource.quantileFun t :=
      integral_sub_half_mul_thetaSource_quantileFun_pos
    _ = ∫ t in Ioo (0 : ℝ) 1, t * thetaSource.quantileFun t := by
      calc
        (∫ t in Ioo (0 : ℝ) 1,
            (t - 1 / 2) * thetaSource.quantileFun t) =
            (∫ t in Ioo (0 : ℝ) 1,
              ((t - 1 / 2) * thetaSource.quantileFun t +
                (1 / 2) * thetaSource.quantileFun t)) := by
              rw [MeasureTheory.integral_add hcint (hqint.const_mul (1 / 2)),
                MeasureTheory.integral_const_mul, integral_quantileFun, mul_zero, add_zero]
        _ = ∫ t in Ioo (0 : ℝ) 1,
            t * thetaSource.quantileFun t := by
              apply setIntegral_congr_fun measurableSet_Ioo
              intro t _
              ring

/-- Pinned dipole of the quantile source is the complexification of a strictly positive integral. -/
theorem pinnedFirstMoment_thetaQuantileCoordinate_eq :
    pinnedFirstMoment thetaQuantileCoordinate =
      ((∫ t in Ioo (0 : ℝ) 1,
        t * thetaSource.quantileFun t : ℝ) : ℂ) := by
  rw [pinnedFirstMoment]
  calc
    (∫ t, (t : ℂ) * thetaQuantileCoordinate t ∂unitIntervalMeasure) =
        ∫ t, ((t * thetaSource.quantileFun t : ℝ) : ℂ)
          ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [thetaQuantileCoordinate_ae] with t ht
      rw [ht]
      exact (Complex.ofReal_mul t (thetaSource.quantileFun t)).symm
    _ = ((∫ t in Ioo (0 : ℝ) 1,
        t * thetaSource.quantileFun t : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, unitIntervalMeasure_eq]

/-- Quantile source carries a strictly positive real dipole. -/
theorem pinnedFirstMoment_thetaQuantileCoordinate_re_pos :
    0 < (pinnedFirstMoment thetaQuantileCoordinate).re := by
  rw [pinnedFirstMoment_thetaQuantileCoordinate_eq, Complex.ofReal_re]
  exact integral_mul_thetaSource_quantileFun_pos

theorem pinnedFirstMoment_thetaQuantileCoordinate_ne_zero :
    pinnedFirstMoment thetaQuantileCoordinate ≠ 0 := by
  exact fun h => (ne_of_gt pinnedFirstMoment_thetaQuantileCoordinate_re_pos)
    (congrArg Complex.re h)

/-- With zero monopole, the centered boundary dipole is the ordinary first moment. -/
theorem pinnedCentered_thetaQuantileCoordinate_eq_firstMoment :
    pinnedCentered thetaQuantileCoordinate =
      pinnedFirstMoment thetaQuantileCoordinate := by
  rw [pinnedCentered, pinnedMean_thetaQuantileCoordinate_eq_zero]
  ring

/-- The incoming amplitude of the quantile source is its negative dipole channel. -/
theorem pinnedInAmplitude_thetaQuantileCoordinate :
    pinnedInAmplitude thetaQuantileCoordinate =
      -pinnedFirstMoment thetaQuantileCoordinate /
        ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [pinnedInAmplitude, pinnedMean_thetaQuantileCoordinate_eq_zero,
    pinnedCentered_thetaQuantileCoordinate_eq_firstMoment]
  ring

/-- The outgoing amplitude of the quantile source is its positive dipole channel. -/
theorem pinnedOutAmplitude_thetaQuantileCoordinate :
    pinnedOutAmplitude thetaQuantileCoordinate =
      pinnedFirstMoment thetaQuantileCoordinate /
        ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [pinnedOutAmplitude, pinnedMean_thetaQuantileCoordinate_eq_zero,
    pinnedCentered_thetaQuantileCoordinate_eq_firstMoment]
  ring

/-- Quantile source is exactly balanced between the two boundary ports. -/
theorem pinnedInAmplitude_thetaQuantileCoordinate_eq_neg_out :
    pinnedInAmplitude thetaQuantileCoordinate =
      -pinnedOutAmplitude thetaQuantileCoordinate := by
  rw [pinnedInAmplitude_thetaQuantileCoordinate,
    pinnedOutAmplitude_thetaQuantileCoordinate]
  ring

/-- Quantile source lies on the null cone of the rank-two boundary Green form. -/
theorem inner_pinnedBoundaryCLM_thetaQuantileCoordinate_eq_zero :
    (inner ℂ (pinnedBoundaryCLM thetaQuantileCoordinate)
      thetaQuantileCoordinate : ℂ) = 0 := by
  rw [inner_pinnedBoundaryCLM_eq_amplitudes,
    pinnedInAmplitude_thetaQuantileCoordinate_eq_neg_out, norm_neg]
  ring

/-- Boundary operator sees only the unresolved dipole of the balanced quantile source. -/
theorem pinnedBoundaryCLM_thetaQuantileCoordinate_eq_dipole :
    pinnedBoundaryCLM thetaQuantileCoordinate =
      -pinnedFirstMoment thetaQuantileCoordinate • pinnedOne := by
  rw [pinnedBoundaryCLM_eq_affine_combination,
    pinnedMean_thetaQuantileCoordinate_eq_zero]
  module

/-- Quantile source is a nonzero lightlike state, not a vector in the boundary kernel. -/
theorem pinnedBoundaryCLM_thetaQuantileCoordinate_ne_zero :
    pinnedBoundaryCLM thetaQuantileCoordinate ≠ 0 := by
  rw [pinnedBoundaryCLM_thetaQuantileCoordinate_eq_dipole]
  exact smul_ne_zero (neg_ne_zero.mpr
    pinnedFirstMoment_thetaQuantileCoordinate_ne_zero) pinnedOne_ne_zero

/-- Cross-polarizing by the lightlike quantile source extracts the monopole exactly. -/
theorem inner_pinnedBoundaryCLM_thetaQuantileCoordinate (g : H) :
    (inner ℂ (pinnedBoundaryCLM thetaQuantileCoordinate) g : ℂ) =
      -pinnedFirstMoment thetaQuantileCoordinate * pinnedMean g := by
  have hdreal :
      (starRingEnd ℂ) (pinnedFirstMoment thetaQuantileCoordinate) =
        pinnedFirstMoment thetaQuantileCoordinate := by
    rw [pinnedFirstMoment_thetaQuantileCoordinate_eq, Complex.conj_ofReal]
  have hone : (inner ℂ pinnedOne g : ℂ) = pinnedMean g := by
    exact thetaPinnedMeanCLM_apply g
  rw [pinnedBoundaryCLM_thetaQuantileCoordinate_eq_dipole,
    inner_smul_left, map_neg, hdreal, hone]

/-- Monopole is the normalized polarized boundary current of the fixed quantile source. -/
theorem pinnedMean_eq_neg_quantileBoundaryCurrent_div (g : H) :
    pinnedMean g =
      -(inner ℂ (pinnedBoundaryCLM thetaQuantileCoordinate) g : ℂ) /
        pinnedFirstMoment thetaQuantileCoordinate := by
  rw [inner_pinnedBoundaryCLM_thetaQuantileCoordinate]
  field_simp [pinnedFirstMoment_thetaQuantileCoordinate_ne_zero]

end

end RHTower.HedenmalmThetaSource
