import GaloisForLFunctions.HTGeometry.SeparatedRayTailPacket
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern

/-!
# Degenerate realizations of the tail-independence interfaces

Both tail-independence interfaces conclude that a coefficient family vanishes.  With an empty
coefficient index the conclusion is automatic, so the interfaces are consistent; their content is
the nondegenerate case, where the nonvanishing locus of a nonzero combination must be infinite.
-/

namespace GaloisForLFunctions.HTGeometry

theorem rayTailCoefficientIndependent_of_isEmpty
    {I P E : Type*} [Fintype I] [IsEmpty I] (a : I → P → E → ℂ) :
    RayTailCoefficientIndependent a := by
  intro c _
  funext i
  exact isEmptyElim i

theorem shiftClockFiberIndependent_of_isEmpty
    {A P : Type*} [Fintype A] [IsEmpty A]
    (shift : A → ℕ) (scale clock : P → ℂ) (m : ℕ) :
    ShiftClockFiberIndependent shift scale clock m := by
  intro U _ d _
  funext ak
  exact isEmptyElim ak.1

end GaloisForLFunctions.HTGeometry
