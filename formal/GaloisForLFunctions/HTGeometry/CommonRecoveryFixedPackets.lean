import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift

/-!
# Fixed formed packets are fixed observer laws

For a common Markov recovery kernel `κ`, the lifted action of a measurable observer map `A`
fixes the formed packet `μ ⊗ κ` exactly when `A` fixes the observer law `μ`: split formation is
injective because the first marginal recovers the observer.
-/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

variable {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]

/-- Split formation is injective on finite observer laws. -/
theorem splitFormation_injective (κ : Kernel X H) [IsMarkovKernel κ] {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : splitFormation μ κ = splitFormation ν κ) :
    μ = ν := by
  rw [← splitFormation_recovers_observer μ κ, h, splitFormation_recovers_observer ν κ]

/-- **Theorem 8.1, fixed packets.**  The lifted action fixes the formed packet exactly when the
observer law is fixed. -/
theorem formationLift_fixed_iff (μ : Measure X) [IsFiniteMeasure μ] (κ : Kernel X H)
    [IsMarkovKernel κ] (A : X → X) (hA : Measurable A) :
    formationLiftKernel κ A hA ∘ₘ splitFormation μ κ = splitFormation μ κ ↔ μ.map A = μ := by
  rw [formationLiftKernel_naturality μ κ A hA]
  constructor
  · exact splitFormation_injective κ
  · intro h; rw [h]

end GaloisForLFunctions.HTGeometry
