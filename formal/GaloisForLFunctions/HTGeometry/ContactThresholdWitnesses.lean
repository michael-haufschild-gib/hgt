import GaloisForLFunctions.HTGeometry.StokesContactTomography

/-!
# The contact threshold relation is reflexive

The threshold relation of a rooted contact tree holds at every diagonal pair by definition, so the
threshold partition it generates is never empty.  It is also monotone in the threshold.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

namespace RootedContactTree

/-- Every index is threshold-related to itself, at every threshold. -/
theorem thresholdRel_refl {n : ℕ} (t : RootedContactTree n) (a : ℝ) (i : Fin n) :
    t.thresholdRel a i i := Or.inl rfl

end RootedContactTree

end IrregularStokes
end GaloisForLFunctions
