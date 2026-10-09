/- Adapted from OpenAI/math (MIT license), commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/AlgebraicGeometry/StableCoordinate/NonzeroFiberAssembly.lean -/

import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.NonzeroFiberTransport
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Presentation

namespace GaloisForLFunctions.HTGeometry

/-!
# Nonzero fibers of the four-variable polynomial

The matrix presentation identifies its distinguished element with exactly
`StableCoordinate.f`.  Composing that presentation with the nonzero-fiber calculation gives an
affine coordinate-algebra isomorphism for every nonzero complex parameter.
-/

noncomputable section

namespace StableCoordinate

/-- Every nonzero complex fiber of the exact polynomial has affine-three-space
coordinate algebra. The zero fiber is treated in `ZeroFiberExact`. -/
def exactNonzeroFiberEquiv (l : ℂ) (hl : l≠0) : FiberRing l ≃ₐ[ℂ] R 3 :=
  NonzeroFiber.transportedFiberEquiv Presentation.originalPresentation f
    Presentation.originalPresentation_p l hl

theorem isAffineThreeSpaceFiber_of_ne_zero (l : ℂ) (hl : l≠0) :
    IsAffineThreeSpaceFiber l :=
  ⟨exactNonzeroFiberEquiv l hl⟩

end StableCoordinate

end

end GaloisForLFunctions.HTGeometry
