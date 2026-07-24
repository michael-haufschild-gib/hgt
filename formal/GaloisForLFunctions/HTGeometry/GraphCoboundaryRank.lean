import GaloisForLFunctions.HTGeometry.GraphCoboundary

/-!
# The rank of the degree-0 coboundary

The image of the degree-`0` simplicial coboundary `δ⁰` is the space of exact `1`-coboundaries; its
dimension is the cut-space dimension of the graph,

`rank δ⁰ = |V| − (number of connected components)`,

the number of edges in a spanning forest.  This follows from rank–nullity together with
`graphCoboundary_ker` (`ker δ⁰ = componentConstant`) and `finrank_componentConstant`
(`dim (componentConstant) = number of components`).  It is the coboundary-rank input to the reduced
first cohomology `H̃¹ = |E| − rank δ⁰ = |E| − |V| + components`.
-/

namespace GaloisForLFunctions

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (F : Type*) [Field F]

/-- **Coboundary rank.**  The rank of the degree-`0` coboundary is `|V| − (number of components)`. -/
theorem finrank_graphCoboundary_range :
    Module.finrank F (LinearMap.range (graphCoboundary G F))
      = Fintype.card V - Fintype.card G.ConnectedComponent := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (graphCoboundary G F)
  rw [graphCoboundary_ker, finrank_componentConstant] at hrn
  have hV : Module.finrank F (V → F) = Fintype.card V := Module.finrank_pi F
  rw [hV] at hrn
  omega

/-- **Spanning-tree edge count.**  For a connected complex the coboundary rank is `|V| − 1`. -/
theorem finrank_graphCoboundary_range_of_connected [Nonempty V] (hG : G.Connected) :
    Module.finrank F (LinearMap.range (graphCoboundary G F)) = Fintype.card V - 1 := by
  have hss : Subsingleton G.ConnectedComponent := by
    constructor
    intro c d
    induction c using ConnectedComponent.ind with
    | _ u =>
      induction d using ConnectedComponent.ind with
      | _ v => exact ConnectedComponent.eq.mpr (hG.preconnected u v)
  have hcard : Fintype.card G.ConnectedComponent = 1 :=
    Fintype.card_eq_one_iff.mpr
      ⟨G.connectedComponentMk (Classical.arbitrary V), fun c => Subsingleton.elim c _⟩
  rw [finrank_graphCoboundary_range, hcard]

end

end GaloisForLFunctions
