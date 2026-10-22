import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyFull
import GaloisForLFunctions.HTGeometry.CriticalOneStepRigidity

/-!
# Unconditional one-step postcritical rigidity

Full critical geometric monodromy removes the final premise from the one-step primitive-generator
theorem.  One raw and one reciprocal postcritical coefficient therefore recover the full source
field extended by the new raw coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- One postcritical reciprocal coefficient unconditionally collapses the entire higher-rank
critical horizon ambiguity over the complex numbers. -/
theorem criticalObservation_sup_postcritical_eq_criticalSourceFieldSup_complex :
    criticalObservationField ℂ m n
        ⊔ IntermediateField.adjoin ℂ {postcriticalRawFieldElement ℂ m n}
        ⊔ IntermediateField.adjoin ℂ {postcriticalReciprocalFieldElement ℂ m n}
      = criticalSourceFieldSup ℂ m n :=
  criticalObservation_sup_postcritical_eq_criticalSourceFieldSup ℂ
    Fact.out Fact.out criticalGeometricMonodromy_eq_top

end

end GaloisForLFunctions.HTGeometry
