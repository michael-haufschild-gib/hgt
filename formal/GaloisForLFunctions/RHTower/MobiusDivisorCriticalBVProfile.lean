import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationRegularity
import GaloisForLFunctions.HTGeometry.BoundedVariationPrimitive

/-! # Global variation of the literal complete Abel clock

The actual velocity is extended by zero before the source starts. Its
primitive is the complete profile, including every arithmetic wall.
-/

noncomputable section
open MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

def criticalAbelGlobalVelocity : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator criticalAbelLogVelocity

theorem integrable_criticalAbelGlobalVelocity : Integrable criticalAbelGlobalVelocity :=
  (integrable_indicator_iff measurableSet_Ioi).mpr integrableOn_criticalAbelLogVelocity

theorem criticalAbelGlobalVelocity_integral (t : ℝ) :
    (∫ u in (0 : ℝ)..t, criticalAbelGlobalVelocity u) = criticalAbelLogProfile t := by
  by_cases ht : 0 ≤ t
  · rw [← criticalAbelLogVelocity_integral ht, intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_of_le ht]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1) _
  · have ht0 := (lt_of_not_ge ht).le
    rw [intervalIntegral.integral_of_ge ht0, criticalAbelLogProfile_zero_of_nonpos ht0]
    have hz : criticalAbelGlobalVelocity =ᵐ[volume.restrict (Ioc t 0)] (fun _ => 0) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from not_lt.mpr hu.2) _
    rw [integral_congr_ae hz, integral_zero, neg_zero]

theorem boundedVariationOn_criticalAbelLogProfile :
    BoundedVariationOn criticalAbelLogProfile univ := by
  simpa only [criticalAbelGlobalVelocity_integral] using
    boundedVariationOn_integral_primitive integrable_criticalAbelGlobalVelocity (0 : ℝ)

theorem eVariationOn_criticalAbelLogProfile_translate_le (t : ℝ) :
    eVariationOn (fun x => criticalAbelLogProfile (t - x)) univ ≤
      eVariationOn criticalAbelLogProfile univ := by
  exact eVariationOn.comp_le_of_antitoneOn criticalAbelLogProfile (fun x => t - x)
    (fun _ _ _ _ h => sub_le_sub_left h t) (fun _ _ => mem_univ _)

theorem boundedVariationOn_criticalAbelLogProfile_translate (t : ℝ) :
    BoundedVariationOn (fun x => criticalAbelLogProfile (t - x)) univ :=
  ne_top_of_le_ne_top boundedVariationOn_criticalAbelLogProfile
    (eVariationOn_criticalAbelLogProfile_translate_le t)

end RHTower
