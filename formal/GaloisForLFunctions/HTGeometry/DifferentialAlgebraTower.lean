import GaloisForLFunctions.HTGeometry.DifferenceDifferential

/-!
# Differential algebra towers

Derivation compatibility composes along a scalar tower. This supplies the canonical
`DifferentialAlgebra` structure needed when a parameterized Picard--Vessiot quotient is viewed
over its field of difference constants rather than only over its rational-coordinate field.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

variable {C K E : Type*} [CommRing C] [CommRing K] [CommRing E]
  [Algebra C K] [Algebra K E] [Algebra C E] [IsScalarTower C K E]
  [Differential C] [Differential K] [Differential E]
  [DifferentialAlgebra C K] [DifferentialAlgebra K E]

include K

/-- Differential-algebra structure maps compose along a scalar tower. -/
theorem differentialAlgebra_trans : DifferentialAlgebra C E := by
  constructor
  intro c
  rw [IsScalarTower.algebraMap_apply C K E,
    DifferentialAlgebra.deriv_algebraMap, DifferentialAlgebra.deriv_algebraMap,
    IsScalarTower.algebraMap_apply C K E]

end GaloisForLFunctions.HTGeometry
