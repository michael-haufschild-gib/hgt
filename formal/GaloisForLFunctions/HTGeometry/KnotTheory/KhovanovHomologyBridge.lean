import GaloisForLFunctions.HTGeometry.KnotTheory.KhovanovFrobenius
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.AbelianDifferentialCharacter

/-!
# Khovanov resolution face in existing additive homology infrastructure

The tensor-coordinate all-merge Khovanov face is packaged as an additive chain complex using the
existing differential-character homology API.  Consequently, each first Khovanov differential is
represented by a zero homology class at the next resolution level.
-/

namespace GaloisForLFunctions.HTGeometry.KnotTheory

open HTGeometry.NomologicalHomotopyGeometry.AbelianDifferentialCharacter

noncomputable section

/-- The linear all-merge Khovanov face, embedded in the existing additive chain-complex API. -/
def khTensorAllMergeAbelianChainComplex :
    ChainComplex KhovanovTensorCube KhovanovTensorCube
      (KhovanovTensorSquare × KhovanovTensorSquare) KhovanovA where
  boundaryNext := 0
  boundary := khTensorMergeD0.toAddMonoidHom
  boundaryPrev := khTensorMergeD1.toAddMonoidHom
  boundary_sq_next := by
    ext t
    simp
  boundary_sq := by
    ext t
    exact khTensorAllMergeResolutionCube.d_squared t

/-- A Khovanov first differential is zero in the existing additive homology quotient. -/
theorem khTensorMergeD0_homologyClass_zero (t : KhovanovTensorCube) :
    khTensorAllMergeAbelianChainComplex.homologyClass
      (khTensorAllMergeAbelianChainComplex.boundaryCycle t) = 0 :=
  khTensorAllMergeAbelianChainComplex.homologyClass_boundaryCycle t

end

end GaloisForLFunctions.HTGeometry.KnotTheory
