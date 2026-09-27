import GaloisForLFunctions.RHTower.CCMThetaPrimeLocalizationMoment
import GaloisForLFunctions.RHTower.CCMThetaExplicitSupportGap

/-!
# A concrete localized coercive piece inside every smooth source

At any center, an explicit bump angle extracts a source with arbitrarily
prescribed physical coercivity. The complementary source vanishes on an
inner neighborhood. The exact arithmetic localization error describes the
remaining interaction with that complement; its proved second-moment bound
gives an unconditional lower bound for the original broad source.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

def ccmTinyLocalizationBump (a : SuzukiPositiveAperture) (L c : ℝ) : ContDiffBump c where
  rIn := ccmExplicitSupportThreshold a L / 8
  rOut := ccmExplicitSupportThreshold a L / 4
  rIn_pos := div_pos (ccmExplicitSupportThreshold_pos a L) (by norm_num)
  rIn_lt_rOut := by linarith [ccmExplicitSupportThreshold_pos a L]

def ccmTinyLocalizationAngle (a : SuzukiPositiveAperture) (L c : ℝ) : 𝓢(ℝ, ℝ) :=
  (Real.pi / 2) • (ccmTinyLocalizationBump a L c).hasCompactSupport.toSchwartzMap
    (ccmTinyLocalizationBump a L c).contDiff

theorem ccmTinyLocalizationAngle_apply (a : SuzukiPositiveAperture) (L c x : ℝ) :
    ccmTinyLocalizationAngle a L c x = Real.pi / 2 * ccmTinyLocalizationBump a L c x := rfl

theorem ccmTinyCosLocalizedSource_eq_zero {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (L c x : ℝ)
    (hx : x ∈ Metric.closedBall c (ccmExplicitSupportThreshold a L / 8)) :
    ccmCosLocalizedSource u (ccmTinyLocalizationAngle a L c) x = 0 := by
  have hb := (ccmTinyLocalizationBump a L c).one_of_mem_closedBall hx
  simp only [ccmCosLocalizedSource_apply, ccmTinyLocalizationAngle_apply, hb, mul_one,
    Real.cos_pi_div_two, Complex.ofReal_zero, zero_mul]

theorem ccmTinySinLocalizedSource_eq_source {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (L c x : ℝ)
    (hx : x ∈ Metric.closedBall c (ccmExplicitSupportThreshold a L / 8)) :
    ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c) x = u x := by
  have hb := (ccmTinyLocalizationBump a L c).one_of_mem_closedBall hx
  simp only [ccmSinLocalizedSource_apply, ccmTinyLocalizationAngle_apply, hb, mul_one,
    Real.sin_pi_div_two, Complex.ofReal_one, one_mul]

theorem ccmTinySinLocalizedSource_support_subset {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (L c : ℝ) :
    Function.support (ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c)) ⊆
      Metric.ball c (ccmExplicitSupportThreshold a L / 4) := by
  intro x hx
  by_contra hout
  have hb : ccmTinyLocalizationBump a L c x = 0 :=
    (ccmTinyLocalizationBump a L c).zero_of_le_dist (le_of_not_gt hout)
  exact hx (by simp only [ccmSinLocalizedSource_apply, ccmTinyLocalizationAngle_apply,
    hb, mul_zero, Real.sin_zero, Complex.ofReal_zero, zero_mul])

theorem ccmTinySinLocalizedSource_supportMeasure_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (L c : ℝ) :
    ccmSmoothSupportMeasure (ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c)) ≤
      ccmExplicitSupportThreshold a L := by
  have hv : volume (Function.support (ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c))) ≤
      volume (Metric.ball c (ccmExplicitSupportThreshold a L / 4)) :=
    measure_mono (ccmTinySinLocalizedSource_support_subset u L c)
  rw [Real.volume_ball] at hv
  have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
  have ht := ccmExplicitSupportThreshold_pos a L
  rw [ENNReal.toReal_ofReal (by positivity)] at hm
  change ccmSmoothSupportMeasure (ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c)) ≤ _ at hm
  linarith [ccmExplicitSupportThreshold_pos a L]

/-- Every source has this concrete local piece with any prescribed coercivity margin. -/
theorem ccmTinySinLocalizedSource_coercivity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (L c : ℝ) :
    L * ‖ccmArchimedeanFormEmbedding a
        (ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c)).toCCMFormVector‖ ^ 2 +
      (1 / 2 : ℝ) * ‖(ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c)).toCCMFormVector‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a
        (ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c)).toCCMFormVector :=
  ccmSmooth_explicitSupport_coercivity a L _ (ccmTinySinLocalizedSource_supportMeasure_le u L c)

/-- Actual local coercivity plus its complete interaction cost inside an arbitrary broad source. -/
theorem ccmRestrictedWeilSourceQuadratic_tinyLocalization_lower_bound
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) (L c : ℝ) :
    ccmRestrictedWeilSourceQuadratic a
        (ccmCosLocalizedSource u (ccmTinyLocalizationAngle a L c)).toCCMFormVector +
      L * ‖ccmArchimedeanFormEmbedding a
        (ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c)).toCCMFormVector‖ ^ 2 +
      (1 / 2 : ℝ) * ‖(ccmSinLocalizedSource u (ccmTinyLocalizationAngle a L c)).toCCMFormVector‖ ^ 2 -
      SchwartzMap.seminorm ℝ 0 1 (ccmTinyLocalizationAngle a L c) ^ 2 *
        (ccmThetaPrimeLocalizationMoment a + ccmThetaContinuousLocalizationMoment a) *
          ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  have hl := ccmRestrictedWeilSourceQuadratic_localization_lower_bound u
    (ccmTinyLocalizationAngle a L c)
  have hc := ccmTinySinLocalizedSource_coercivity u L c
  linarith

end RHTower
