import GaloisForLFunctions.HTGeometry.DifferentialVariationalOreModule
import GaloisForLFunctions.HTGeometry.DifferentialVariationalRankOneBuilding

/-!
# Triviality of every rank-one variational action

The full correctly oriented projective lattice carrier has one point in rank one.  Therefore every
canonical differential-automorphism action constructed from a one-element operator basis is the
identity.  This is the exact geometric rank-one no-displacement conclusion.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

namespace DifferentialFieldAut

/-- Every differential automorphism fixes every rank-one projective lattice point. -/
theorem projectiveBuildingAction_rankOne
    (σ : DifferentialFieldAut C K)
    (b : Module.Basis (Fin 1) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin 1)) :
    projectiveBuildingAction σ b x = x :=
  Subsingleton.elim _ _

/-- Every rank-one projective building equivalence is the identity. -/
theorem projectiveBuildingEquiv_rankOne
    (σ : DifferentialFieldAut C K)
    (b : Module.Basis (Fin 1) (DiffOp K) (VariationalOreModule C K)) :
    projectiveBuildingEquiv σ b = Equiv.refl _ := by
  ext x
  exact projectiveBuildingAction_rankOne σ b x

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
