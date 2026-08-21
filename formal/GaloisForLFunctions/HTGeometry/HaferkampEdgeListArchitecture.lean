import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitArchitecture

/-!
# Ordered edge-list architectures for Haferkamp blocks

The paper treats a block as an ordered list of two-qubit locations. This file
turns that list into the corpus's `TwoQubitArchitecture` and unfolds its
contraction to the literal product of lifted local gates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace TwoQubitArchitecture

/-- Build a two-qubit architecture from an ordered list of distinct directed
qubit pairs. -/
def ofEdgeList {n : ℕ} (edges : List (Fin n × Fin n))
    (hdistinct : ∀ e ∈ edges, e.1 ≠ e.2) :
    TwoQubitArchitecture n edges.length where
  sites r := edges.get r
  distinct r := hdistinct (edges.get r) (List.get_mem _ _)

/-- The contraction of an edge-list architecture is the corresponding ordered
product of its lifted local gates. -/
theorem ofEdgeList_contraction
    {n : ℕ} (edges : List (Fin n × Fin n))
    (hdistinct : ∀ e ∈ edges, e.1 ≠ e.2)
    (gates : Fin edges.length → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    (ofEdgeList edges hdistinct).contraction gates =
      (List.ofFn fun r =>
        twoQubitLift (edges.get r).1 (edges.get r).2
          (hdistinct (edges.get r) (List.get_mem _ _)) (gates r)).prod := rfl

end TwoQubitArchitecture

end

end GaloisForLFunctions.HTGeometry
