import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalL2Closure
import GaloisForLFunctions.HTGeometry.FriedrichsFormOperator

/-!
# Compact-resolvent form operator on the cuspidal finite-deck carrier

The compact cusp/core form embedding determines a canonical self-adjoint
Friedrichs operator on the closed cuspidal `L²` carrier.  Its resolvent at
zero is compact.  The next leaf identifies this operator with the literal
finite-deck Maass Laplacian on a dense smooth core.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Canonical compact-resolvent operator associated to the cuspidal form norm. -/
def cuspidalFriedrichsOperator (N : ℕ) : CuspidalL2 N →ₗ.[ℂ] CuspidalL2 N :=
  friedrichsFormOperator (cuspidalFormInclusionClosure N)

theorem cuspidalFriedrichsOperator_isSelfAdjoint (N : ℕ) :
    IsSelfAdjoint (cuspidalFriedrichsOperator N) := by
  exact friedrichsFormOperator_isSelfAdjoint _
    (cuspidalFormInclusionClosure_injective N)
    (cuspidalFormInclusionClosure_dense_range N)

theorem cuspidalFriedrichsOperator_hasCompactResolventAt_zero (N : ℕ) :
    LinearPMap.HasCompactResolventAt (cuspidalFriedrichsOperator N) 0 := by
  exact friedrichsFormOperator_hasCompactResolventAt_zero _
    (cuspidalFormInclusionClosure_injective N)
    (cuspidalFormInclusionClosure_dense_range N)
    (isCompactOperator_cuspidalFormInclusionClosure N)

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
