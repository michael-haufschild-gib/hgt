import GaloisForLFunctions.HTGeometry.TorusFormalityColimit

/-!
# The directed systems of a tower of tori

The de Rham algebras of a tower of tori and the exterior algebras of the duals of its covering
spaces form directed systems: the transition morphism of a reflexive relation is the identity and
the transition morphisms compose, because the lifts of the covering maps do.  In each degree this
makes the underlying modules a directed system, which is what the colimit of the algebras consumes.

* `GaloisForLFunctions.HTGeometry.torusSystemDirectedDeg` : the periodic forms in each degree.
* `GaloisForLFunctions.HTGeometry.exteriorSystemDirectedDeg` : the exterior powers in each degree.
-/

universe u v

namespace GaloisForLFunctions.HTGeometry

section Instances

variable {𝕜 : Type u} [RCLike 𝕜] {p : 𝕜} {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [DecidableEq ι] (S : TorusCoverSystem 𝕜 p ι)

/-- The periodic forms of a tower of tori form a directed system in every degree. -/
instance torusSystemDirectedDeg (n : ℕ) :
    DirectedSystem (fun i => smoothPeriodicForms p (S.dim i) n)
      (fun i j h => degTransition (torusSystemHom S) n i j h) :=
  directedSystem_deg (torusSystemHom S) (torusSystem_directed S) n

/-- The exterior powers of the duals of the covering spaces form a directed system in every
degree. -/
instance exteriorSystemDirectedDeg (n : ℕ) :
    DirectedSystem (fun i => ⋀[𝕜]^n (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜)))
      (fun i j h => degTransition (exteriorSystemHom S) n i j h) :=
  directedSystem_deg (exteriorSystemHom S) (exteriorSystem_directed S) n

end Instances

end GaloisForLFunctions.HTGeometry
