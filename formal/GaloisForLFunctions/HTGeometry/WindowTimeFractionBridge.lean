/-
# The window sampling law is the quenched time fraction

The uniformly sampled observation time on `(0,T]` and the quenched time fraction of a joint event
are the same number, so a completed-time density bound proved through the sampling law feeds the
quenched-to-fixed-time transfer directly.

Main results:
* `quenchedTimeFraction_eq_windowProbability` — the two normalizations agree on every positive
  window.
* `limsup_quenchedTimeFraction_eq_limsup_windowProbability` — hence so do their upper limits.
-/
import GaloisForLFunctions.HTGeometry.QuenchedFixedTimeTransfer
import GaloisForLFunctions.HTGeometry.CompletedTimeBohrMean

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The quenched time fraction is the sampling probability of the fibre. -/
theorem quenchedTimeFraction_eq_windowProbability (S : Set (Ω × ℝ)) (J : Ω) {T : ℝ} (hT : 0 < T) :
    quenchedTimeFraction S J T
      = (windowProbabilityMeasure T : Measure ℝ) (Prod.mk J ⁻¹' S) := by
  rw [quenchedTimeFraction, windowProbabilityMeasure]
  show volume (Prod.mk J ⁻¹' S ∩ Ioc 0 T) / ENNReal.ofReal T
      = ((ENNReal.ofReal (windowLength T))⁻¹ •
          volume.restrict (Set.Ioc 0 (windowLength T))) (Prod.mk J ⁻¹' S)
  rw [windowLength_eq hT, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' measurableSet_Ioc, ENNReal.div_eq_inv_mul]

/-- The two upper limits agree. -/
theorem limsup_quenchedTimeFraction_eq_limsup_windowProbability (S : Set (Ω × ℝ)) (J : Ω) :
    atTop.limsup (fun T => quenchedTimeFraction S J T)
      = atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ) (Prod.mk J ⁻¹' S)) := by
  refine limsup_congr ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact quenchedTimeFraction_eq_windowProbability S J hT

/-- **The transfer hypothesis, in sampling form.**  A completed-time density bound on the fibre of
the complement supplies the hypothesis of the quenched-to-fixed-time transfer. -/
theorem le_liminf_quenchedTimeFraction_of_windowProbability {S : Set (Ω × ℝ)}
    (hS : MeasurableSet S) (J : Ω) {η : ℝ≥0∞}
    (h : atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ)
      (Prod.mk J ⁻¹' Sᶜ)) ≤ η) :
    1 - η ≤ liminf (fun T => quenchedTimeFraction S J T) atTop := by
  refine le_liminf_quenchedTimeFraction_of_limsup_compl_le hS J ?_
  rwa [limsup_quenchedTimeFraction_eq_limsup_windowProbability]

end GaloisForLFunctions.HTGeometry

end
