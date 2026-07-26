import GaloisForLFunctions.HTGeometry.PrimeClockAnalyticEulerCompletion
import GaloisForLFunctions.HTGeometry.UpperEndRationalCoordinateDifferentialAdjoin

/-!
# The upper-end differential instance stack

Every module that works with the upper-end meromorphic field as a differential algebra needs the
same eight instances: the analytic subring is a domain, the meromorphic field is a characteristic
zero `ℂ`-algebra with its canonical derivation, the rational coordinate subfield and the analytic
scalar valuation layer are derivation-closed hence differential, and both sit inside the meromorphic
field as differential algebras.

These are data-carrying classes, so they are *scoped* rather than global: a module opts in with
`open scoped UpperEndDifferentialInstances` and modules that do not opt in see no change to instance
resolution.
-/

open scoped Differential
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace UpperEndDifferentialInstances

noncomputable section

scoped instance upperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

scoped instance upperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

scoped instance upperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

scoped instance upperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

scoped instance coordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

scoped instance coordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

scoped instance allValuationFieldDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

scoped instance allValuationFieldDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

end

end UpperEndDifferentialInstances

open scoped UpperEndDifferentialInstances

namespace UpperEndComplexTowerInstances

noncomputable section

/-- The complex numbers carry the zero derivation, so every upper-end differential statement can be
read relative to `ℂ` as the constant field. -/
scoped instance complexDifferential : Differential ℂ where
  deriv := 0

scoped instance complexDifferentialAlgebra :
    DifferentialAlgebra ℂ upperEndMeroField :=
  ⟨fun c ↦ by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [map_zero]⟩

/-- The rational coordinate field sits between `ℂ` and the meromorphic field compatibly, since both
structure maps are the inclusion. -/
scoped instance complexCoordinateScalarTower :
    IsScalarTower ℂ upperEndRationalCoordinateField upperEndMeroField :=
  .of_algebraMap_eq fun _ ↦ rfl

end

end UpperEndComplexTowerInstances
