import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveIwahori
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientGroup

/-!
# Free coordinates of completed positive unipotent matrices

The commutative-ring coordinate equivalence specializes to the actual
positive unipotent subgroup used by the central loop splitting.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable (F : Type*) [Field F]

/-- Three independent entries, with upper-left residue one and lower-left residue zero. -/
abbrev PositiveUnipotentCoordinates := UnipotentCoefficientCoordinates F

/-- Build the actual positive unipotent matrix from its three free entries. -/
def positiveUnipotentOfCoordinates (p : PositiveUnipotentCoordinates F) :
    positiveUnipotentMatrices F := unipotentCoefficientOfCoordinates F p

/-- Read the upper-left, upper-right and lower-left entries. -/
def positiveUnipotentToCoordinates (g : positiveUnipotentMatrices F) :
    PositiveUnipotentCoordinates F := unipotentCoefficientToCoordinates F g

/-- The completed positive unipotent group has three independent power-series entries. -/
def positiveUnipotentCoordinateEquiv :
    positiveUnipotentMatrices F ≃ PositiveUnipotentCoordinates F := unipotentCoefficientEquiv F

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.positiveUnipotentCoordinateEquiv
