/- Adapted from OpenAI/math (MIT license), commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/AlgebraicGeometry/StableCoordinate/AllFibers.lean -/

import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.NonzeroFiberAssembly
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ZeroFiberExact
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Rectifiability

namespace GaloisForLFunctions.HTGeometry

/-!
# Every complex fiber of the exact polynomial

The two explicit quotient-algebra calculations cover every parameter, including
zero. Together with the noncoordinate theorem, these equivalences show that every
fiber is affine three-space and its embedding is nonrectifiable.
-/

namespace StableCoordinate

/-- Every complex fiber of the specified polynomial has the coordinate algebra
of affine three-space, with no exceptional parameters. -/
theorem all_fibers_isAffineThreeSpace :
    ∀ t : ℂ, IsAffineThreeSpaceFiber t := by
  intro t
  by_cases ht : t = 0
  · subst t
    exact zeroFiber_isAffineThreeSpace
  · exact isAffineThreeSpaceFiber_of_ne_zero t ht

/-- An actual complex algebra equivalence for each fiber. -/
noncomputable def exactFiberEquiv (t : ℂ) : FiberRing t ≃ₐ[ℂ] R 3 :=
  Classical.choice (all_fibers_isAffineThreeSpace t)

/-- With the unrestricted four-variable coordinate obstruction, the already
proved all-fiber calculation supplies the entire geometric principal group. -/
theorem fiberPackage_of_noncoordinate
    (h : ¬ IsCoordinate (by decide : 0 < 4) f) : FiberPackage :=
  fiberPackage_of_noncoordinate_of_affine h all_fibers_isAffineThreeSpace

end StableCoordinate

end GaloisForLFunctions.HTGeometry
