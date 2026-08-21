import GaloisForLFunctions.HTGeometry.KnotTheory.ChordData
import GaloisForLFunctions.HTGeometry.KnotTheory.RMatrix

/-!
# A Vassiliev application of framed braid writhe

Resolving two local singular crossings into signed braid crossings turns the existing framed braid
writhe into an integer observable.  Its alternating second singular extension vanishes, so this
is exact degree-one Vassiliev data for the framed braid convention.  It is not an unframed knot
invariant: writhe changes under a Reidemeister-I move.
-/

namespace GaloisForLFunctions.HTGeometry.KnotTheory

/-- Resolve a local singular crossing as a positive or negative braid crossing. -/
def resolutionCrossingSign : Bool → CrossingSign
  | true => .positive
  | false => .negative

/-- The two local resolutions form a two-generator framed braid word. -/
def twoSingularBraidWord (resolutions : LocalResolution 2) : BraidWord 1 :=
  [(0, resolutionCrossingSign (resolutions 0)),
    (0, resolutionCrossingSign (resolutions 1))]

/-- Writhe evaluated after resolving a pair of singular crossings. -/
def framedWritheObservable (resolutions : LocalResolution 2) : ℤ :=
  braidWrithe (twoSingularBraidWord resolutions)

/-- Framed braid writhe has vanishing second Vassiliev difference. -/
theorem framedWrithe_vassiliev_order_one :
    IsTwoSingularVassilievOrderAtMostOne framedWritheObservable := by
  simp [IsTwoSingularVassilievOrderAtMostOne, twoSingularAlternatingExtension,
    framedWritheObservable, twoSingularBraidWord, resolutionCrossingSign,
    twoCrossingResolution, braidWrithe, crossingWrithe]

end GaloisForLFunctions.HTGeometry.KnotTheory
