import GaloisForLFunctions.HTGeometry.PaperFiniteObservationLaw
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Comparison
import GaloisForLFunctions.HTGeometry.ResetPathSingularity
import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry

/-! # Exact relative entropy for finite observations

The paper's support-domination relation is exactly absolute continuity of
finite probability measures. Its real relative entropy agrees with the native
extended divergence on that support domain. Finite observations therefore
inherit the native source's information budget.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory InformationTheory FourierLLogL
open scoped BigOperators ENNReal Classical

variable {Ω α : Type*} [MeasurableSpace Ω]
  [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The paper's finite support condition is exactly measure absolute continuity. -/
theorem paperFiniteMeasureLaw_dominated_iff (μ ν : ProbabilityMeasure α) :
    (paperFiniteMeasureLaw μ).dominated (paperFiniteMeasureLaw ν) ↔
      (μ : Measure α) ≪ (ν : Measure α) := by
  constructor
  · intro h
    apply ResetDilation.absolutelyContinuous_of_singleton
    intro a hz
    by_contra hp
    have hpos := h a (ENNReal.toReal_pos hp (measure_ne_top (μ : Measure α) {a}))
    simp only [paperFiniteMeasureLaw_apply, Measure.real, hz, ENNReal.toReal_zero,
      lt_self_iff_false] at hpos
  · intro h a hp
    apply ENNReal.toReal_pos _ (measure_ne_top (ν : Measure α) {a})
    intro hz
    have hm := h hz
    simp only [paperFiniteMeasureLaw_apply, Measure.real, hm, ENNReal.toReal_zero,
      lt_self_iff_false] at hp

/-- Exact conversion, including the singular-support case. -/
theorem paperFiniteMeasureLaw_klDiv (μ ν : ProbabilityMeasure α) :
    klDiv (μ : Measure α) (ν : Measure α) =
      if (paperFiniteMeasureLaw μ).dominated (paperFiniteMeasureLaw ν)
      then ENNReal.ofReal ((paperFiniteMeasureLaw μ).kl (paperFiniteMeasureLaw ν)) else ∞ := by
  classical
  split_ifs with h
  · have hac := (paperFiniteMeasureLaw_dominated_iff μ ν).mp h
    rw [ResetDilation.klDiv_countable_of_summable (fun a hz => hac hz)
      (hasSum_fintype _).summable, tsum_fintype, Law.kl_ex, Law.Ex]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    change paperFiniteMeasureLaw μ a *
        Real.log (paperFiniteMeasureLaw μ a / paperFiniteMeasureLaw ν a) = _
    by_cases hp : paperFiniteMeasureLaw μ a = 0
    · simp only [hp, zero_mul]
    · have hq := h a (lt_of_le_of_ne ((paperFiniteMeasureLaw μ).nonneg a) (Ne.symm hp))
      rw [Real.log_div hp hq.ne']
  · exact klDiv_of_not_ac ((paperFiniteMeasureLaw_dominated_iff μ ν).not.mp h)

/-- Every finite observation has at most the original source's extended information cost. -/
theorem paperFiniteObservationLaw_kl_le_native
    (μ ν : ProbabilityMeasure Ω) (f : SimpleFunc Ω α) :
    ENNReal.ofReal ((paperFiniteObservationLaw μ f).kl (paperFiniteObservationLaw ν f)) ≤
      klDiv (μ : Measure Ω) (ν : Measure Ω) := by
  have hmap := klDiv_map_le_arbitrary (μ : Measure Ω) (ν : Measure Ω) f f.measurable
  change klDiv ((μ.map f.aemeasurable : ProbabilityMeasure α) : Measure α)
    ((ν.map f.aemeasurable : ProbabilityMeasure α) : Measure α) ≤ _ at hmap
  rw [paperFiniteMeasureLaw_klDiv (μ.map f.aemeasurable) (ν.map f.aemeasurable)] at hmap
  split_ifs at hmap
  · exact hmap
  · exact le_trans le_top hmap

end
end GaloisForLFunctions.HTGeometry
