import GaloisForLFunctions.HTGeometry.PaperFourierLawMeasure
import GaloisForLFunctions.HTGeometry.PaperFiniteObservationEntropy

/-! # Finite atomic laws preserve relative entropy

Realizing a finite law as an atomic probability measure and then reading its atom masses
recovers the law exactly. Absolute continuity and extended relative entropy therefore agree
with the paper's support domination and real relative entropy, including singular supports.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory InformationTheory FourierLLogL
open scoped ENNReal Classical

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem paperFiniteMeasureLaw_atomicProbability (P : Law α) :
    paperFiniteMeasureLaw (P.atomicProbability id) = P := by
  apply Law.ext_of_Ex
  intro f
  rw [paperFiniteMeasureLaw_Ex, Law.integral_atomicProbability]
  rfl

theorem paperAtomicLaw_absolutelyContinuous_iff (P Q : Law α) :
    (P.atomicProbability id : Measure α) ≪ (Q.atomicProbability id : Measure α) ↔
      P.dominated Q := by
  rw [← paperFiniteMeasureLaw_dominated_iff,
    paperFiniteMeasureLaw_atomicProbability, paperFiniteMeasureLaw_atomicProbability]

theorem paperAtomicLaw_klDiv (P Q : Law α) :
    klDiv (P.atomicProbability id : Measure α) (Q.atomicProbability id : Measure α) =
      if P.dominated Q then ENNReal.ofReal (P.kl Q) else ∞ := by
  rw [paperFiniteMeasureLaw_klDiv,
    paperFiniteMeasureLaw_atomicProbability, paperFiniteMeasureLaw_atomicProbability]

end
end GaloisForLFunctions.HTGeometry
