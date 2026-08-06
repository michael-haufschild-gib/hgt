import GaloisForLFunctions.HTGeometry.LocalNoetherianNormalDVR
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Local rings of a normal scheme in codimension one

The Krull dimension of the local ring of a scheme at a point is the codimension of that point, so
a scheme whose affine charts have integrally closed sections has discrete valuation rings as its
local rings at every codimension-one point.  That is the input the pullback law for orders of
vanishing requires, and it is the scheme-level counterpart of the statement that a Noetherian
integrally closed domain localised at a height-one prime is a discrete valuation ring.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **The local ring at a codimension-one point of a normal scheme is a discrete valuation
ring.** -/
theorem isDiscreteValuationRing_stalk {z : X} (hz : coheight z = 1)
    [IsIntegrallyClosed (X.presheaf.stalk z)] :
    IsDiscreteValuationRing (X.presheaf.stalk z) :=
  isDiscreteValuationRing_of_ringKrullDim_eq_one
    (by rw [ringKrullDim_stalk_eq_coheight, hz]; rfl)

omit [IsLocallyNoetherian X] in
/-- The local ring at a point of an affine open with integrally closed sections is integrally
closed. -/
theorem isIntegrallyClosed_stalk_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    [IsIntegrallyClosed Γ(X, U)] (x : U) :
    IsIntegrallyClosed (X.presheaf.stalk x.1) := by
  haveI : Nonempty U := ⟨x⟩
  haveI := hU.isLocalization_stalk x
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x.1)
    (hU.primeIdealOf x).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

/-- **A normal scheme has discrete valuation rings as its local rings in codimension one.** -/
theorem isDiscreteValuationRing_stalk_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    [IsIntegrallyClosed Γ(X, U)] (x : U) (hz : coheight (x.1 : X) = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x.1) :=
  haveI := isIntegrallyClosed_stalk_of_isAffineOpen hU x
  isDiscreteValuationRing_stalk hz

end GaloisForLFunctions.HTGeometry
