import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Rectifiability
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.NonCoordinate

/-!
# Every fiber of the stable coordinate is nonrectifiable

`noncoordinate_implies_all_fibers_nonrectifiable` reduced rectifiability of every complex fiber
`f = t` to `f` being a coordinate of `ℂ[x₀, …, x₃]`; `f_not_coordinate` refutes that.
-/

namespace GaloisForLFunctions.HTGeometry

namespace StableCoordinate

/-- No complex fiber of `f` can be rectified by an automorphism of affine four-space. -/
theorem all_fibers_nonrectifiable : ∀ t : ℂ, ¬ IsRectifiableFiber t :=
  noncoordinate_implies_all_fibers_nonrectifiable f_not_coordinate

end StableCoordinate

end GaloisForLFunctions.HTGeometry
