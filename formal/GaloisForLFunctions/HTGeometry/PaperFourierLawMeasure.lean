import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Law
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Exact atomic probability measures for the source finite laws

Finite laws produce genuine probability measures on any measurable target. Every real
observable is integrable and its integral is exactly the source finite expectation.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Law
noncomputable section
variable {α β : Type*} [Fintype α] [MeasurableSpace β]

/-- Place the source law's masses at the specified target points. -/
def atomicProbability (P : Law α) (φ : α → β) : ProbabilityMeasure β :=
  ⟨∑ i, ENNReal.ofReal (P i) • Measure.dirac (φ i), ⟨by
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => P.nonneg i), P.total,
      ENNReal.ofReal_one]⟩⟩

variable [MeasurableSingletonClass β]

theorem integrable_atomicProbability (P : Law α) (φ : α → β) (f : β → ℝ) :
    Integrable f (P.atomicProbability φ : Measure β) := by
  change Integrable f (∑ i, ENNReal.ofReal (P i) • Measure.dirac (φ i))
  exact integrable_finsetSum_measure.mpr fun _ _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

/-- No measurability or integrability premise is needed for a finite atomic law. -/
theorem integral_atomicProbability (P : Law α) (φ : α → β) (f : β → ℝ) :
    (∫ x, f x ∂(P.atomicProbability φ : Measure β)) = P.Ex (fun i => f (φ i)) := by
  change (∫ x, f x ∂(∑ i, ENNReal.ofReal (P i) • Measure.dirac (φ i))) = _
  rw [integral_finsetSum_measure (fun _ _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (P.nonneg _),
    smul_eq_mul]
  rfl

end
end GaloisForLFunctions.HTGeometry.FourierLLogL.Law
