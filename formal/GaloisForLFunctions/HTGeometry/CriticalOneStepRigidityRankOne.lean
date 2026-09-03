import GaloisForLFunctions.HTGeometry.CoRankOneCriticalMonodromy
import GaloisForLFunctions.HTGeometry.CriticalOneStepRigidity

/-!
# Unconditional one-step postcritical rigidity at every rank-one horizon

The centered-generic descriptions of both rank-one directions discharge the full-monodromy input
of one-step rigidity over every algebraically closed characteristic-zero ground field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- Left-rank-one one-step rigidity over every algebraically closed characteristic-zero field. -/
theorem criticalObservation_sup_postcritical_eq_criticalSourceFieldSup_one_left
    (hn : 0 < n) :
    criticalObservationField K 1 n
        ⊔ IntermediateField.adjoin K {postcriticalRawFieldElement K 1 n}
        ⊔ IntermediateField.adjoin K {postcriticalReciprocalFieldElement K 1 n}
      = criticalSourceFieldSup K 1 n :=
  criticalObservation_sup_postcritical_eq_criticalSourceFieldSup K
    (by omega) hn (criticalGeometricMonodromy_one_left_eq_top (K := K) hn)

/-- Right-rank-one one-step rigidity over every algebraically closed characteristic-zero field. -/
theorem criticalObservation_sup_postcritical_eq_criticalSourceFieldSup_one_right
    (hm : 0 < m) :
    criticalObservationField K m 1
        ⊔ IntermediateField.adjoin K {postcriticalRawFieldElement K m 1}
        ⊔ IntermediateField.adjoin K {postcriticalReciprocalFieldElement K m 1}
      = criticalSourceFieldSup K m 1 :=
  criticalObservation_sup_postcritical_eq_criticalSourceFieldSup K
    hm (by omega) (criticalGeometricMonodromy_one_right_eq_top (K := K) hm)

end

end GaloisForLFunctions.HTGeometry
