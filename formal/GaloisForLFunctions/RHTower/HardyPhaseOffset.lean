import GaloisForLFunctions.RHTower.HardyPhaseIntegrableError
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex Filter Topology MeasureTheory Set
noncomputable section
namespace RHTower

/-- The fixed offset of the actual global Hardy phase from its conductor model. -/
def gammaHardyPhaseOffset : ℝ :=
  limUnder atTop (fun t : ℝ => gammaHardyTheta t - gammaHardyThetaMain t)

private theorem integrable_hardyRateTail {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 13 / t ^ 2) (Ioi a) := by
  have h : IntegrableOn (fun t : ℝ => 13 * t ^ (-2 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha).const_mul 13
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  change 13 * x ^ (-2 : ℝ) = 13 / x ^ 2
  rw [Real.rpow_neg (ha.trans hx).le, Real.rpow_two, div_eq_mul_inv]

private theorem integral_hardyRateTail {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi a, 13 / t ^ 2) = 13 / a := by
  have he : (∫ t : ℝ in Ioi a, 13 / t ^ 2) =
      ∫ t : ℝ in Ioi a, 13 * t ^ (-2 : ℝ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.rpow_neg (ha.trans ht).le, Real.rpow_two, div_eq_mul_inv]
  rw [he, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
  norm_num [Real.rpow_neg_one]
  ring

private theorem integrable_hardyRateError {a : ℝ} (ha : 4 ≤ a) :
    IntegrableOn (fun t : ℝ => gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2)
      (Ioi a) := by
  have hm : Measurable (fun t : ℝ => gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2) :=
    continuous_gammaHardyPhaseRate.measurable.sub
      ((Real.measurable_log.comp (measurable_id.div_const _)).div_const _)
  apply (integrable_hardyRateTail (show 0 < a by linarith)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact gammaHardyPhaseRate_sub_log_conductor_integrable_bound (ha.trans ht.le)

/-- The phase error converges to one fixed real offset, without choosing a
numerical value for that offset. -/
theorem tendsto_gammaHardyTheta_sub_main_offset :
    Tendsto (fun t : ℝ => gammaHardyTheta t - gammaHardyThetaMain t) atTop
      (𝓝 gammaHardyPhaseOffset) := by
  apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 4)
    (f' := fun t => gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2)
  · intro t ht
    exact (hasDerivAt_gammaHardyTheta t).sub
      (hasDerivAt_gammaHardyThetaMain (by have : 4 < t := ht; linarith))
  · exact integrable_hardyRateError (le_refl 4)

/-- A quantitative tail bound keeps the common oscillatory orientation:
the actual phase differs from its conductor model and fixed offset by O(1/t). -/
theorem abs_gammaHardyTheta_sub_main_sub_offset_le {t : ℝ} (ht : 4 ≤ t) :
    |gammaHardyTheta t - gammaHardyThetaMain t - gammaHardyPhaseOffset| ≤ 13 / t := by
  have ht0 : 0 < t := by linarith
  have hi := integrable_hardyRateError ht
  have hq := integrable_hardyRateTail ht0
  have he := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun x : ℝ => gammaHardyTheta x - gammaHardyThetaMain x)
    (f' := fun x => gammaHardyPhaseRate x - Real.log (x / (2 * Real.pi)) / 2)
    (a := t) (fun x hx => (hasDerivAt_gammaHardyTheta x).sub
      (hasDerivAt_gammaHardyThetaMain (ht0.trans_le hx))) hi
    tendsto_gammaHardyTheta_sub_main_offset
  calc
    _ = ‖∫ x : ℝ in Ioi t, gammaHardyPhaseRate x - Real.log (x / (2 * Real.pi)) / 2‖ := by
      rw [he, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ ∫ x : ℝ in Ioi t, ‖gammaHardyPhaseRate x - Real.log (x / (2 * Real.pi)) / 2‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi t, 13 / x ^ 2 :=
      setIntegral_mono_on hi.norm hq measurableSet_Ioi (fun x hx => by
        rw [Real.norm_eq_abs]
        exact gammaHardyPhaseRate_sub_log_conductor_integrable_bound (ht.trans hx.le))
    _ = 13 / t := integral_hardyRateTail ht0

end RHTower
