import GaloisForLFunctions.HTGeometry.SeibergWitten.FlatClifford
import GaloisForLFunctions.HTGeometry.SeibergWitten.Connections

/-!
# Flat chiral Dirac contraction

This module turns the verified flat chiral Clifford matrices into the contraction required by the
mathlib `CovariantDerivative` interface.  Given any genuine covariant derivative on the constant
positive spinor bundle over Euclidean four-space, `flatChiralDirac` is its chiral Dirac operator.
The displayed formula is the finite sum of Clifford multiplication by the four coordinate basis
vectors applied to the covariant derivative in that direction.

No particular covariant derivative is asserted to exist here: this module provides the exact
Dirac construction once such a geometric connection is supplied.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Coordinate basis vector of Euclidean four-space. -/
def flatFourBasis (i : Fin 4) : FourSpace :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm (Pi.basisFun ℝ (Fin 4) i)

/-- Clifford contraction of a one-form with values in the flat positive spinor bundle. -/
def flatCliffordContraction :
    CliffordContractionData FourSpace flatPositiveSpinorBundle flatNegativeSpinorBundle where
  contract := fun _ derivative =>
    ∑ i, flatCliffordPlus (flatFourBasis i) (derivative (flatFourBasis i))

/-- Chiral Dirac operator induced by any smooth connection on the flat positive spinor bundle. -/
def flatChiralDirac
    (connection : SmoothSpinorConnection FourSpace flatPositiveSpinorBundle)
    (sigma : ∀ x, flatPositiveSpinorBundle x) : ∀ x, flatNegativeSpinorBundle x :=
  connection.dirac flatCliffordContraction sigma

/-- Coordinate formula for the flat chiral Dirac contraction. -/
theorem flatChiralDirac_apply
    (connection : SmoothSpinorConnection FourSpace flatPositiveSpinorBundle)
    (sigma : ∀ x, flatPositiveSpinorBundle x) (x : FourSpace) :
    flatChiralDirac connection sigma x =
      ∑ i, flatCliffordPlus (flatFourBasis i)
        (connection.covariantDerivative sigma x (flatFourBasis i)) :=
  rfl

end GaloisForLFunctions.HTGeometry.SeibergWitten
