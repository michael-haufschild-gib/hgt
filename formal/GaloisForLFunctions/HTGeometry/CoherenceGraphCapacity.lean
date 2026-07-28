import GaloisForLFunctions.HTGeometry.GraphCoboundary

/-!
# Exact phase capacity of a finite coherence graph

The phase difference map of a finite graph is its degree-zero coboundary.
Its kernel consists exactly of phases constant on connected components.
Rank-nullity therefore gives an exact, field-independent capacity law:

`phase capacity = number of vertices - number of connected components`.

This is the topological half of the coherence-graph recurrence law.  It does
not identify capacity with the arithmetic rank explored by one particular
Hamiltonian trajectory.
-/

namespace GaloisForLFunctions

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (F : Type*) [Field F]

/-- **Finite coherence-graph capacity law.**  The range of the graph phase
coboundary has dimension `|V|-c(G)` over every coefficient field. -/
theorem finrank_range_graphCoboundary :
    Module.finrank F (LinearMap.range (graphCoboundary G F)) =
      Fintype.card V - Fintype.card G.ConnectedComponent := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (graphCoboundary G F)
  rw [graphCoboundary_ker, finrank_componentConstant] at h
  have hdomain : Module.finrank F (V → F) = Fintype.card V :=
    Module.finrank_pi F
  rw [hdomain] at h
  omega

end

end GaloisForLFunctions
