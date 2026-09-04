import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromyAllFields
import GaloisForLFunctions.HTGeometry.CriticalOneStepRigidity

/-!
# Unconditional one-step critical rigidity over all coefficient fields
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One postcritical reciprocal coefficient unconditionally collapses the entire critical horizon
ambiguity over every algebraically closed characteristic-zero field. -/
theorem criticalObservation_sup_postcritical_eq_criticalSourceFieldSup_charZero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalObservationField K m n
        ⊔ IntermediateField.adjoin K {postcriticalRawFieldElement K m n}
        ⊔ IntermediateField.adjoin K {postcriticalReciprocalFieldElement K m n}
      = criticalSourceFieldSup K m n :=
  criticalObservation_sup_postcritical_eq_criticalSourceFieldSup K hm hn
    (criticalGeometricMonodromy_eq_top_charZero K hm hn)

end

end GaloisForLFunctions.HTGeometry
