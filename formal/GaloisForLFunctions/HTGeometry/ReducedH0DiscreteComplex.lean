import GaloisForLFunctions.HTGeometry.ReducedH0Components

/-!
# Reduced `H⁰` at the two extreme complexes

Two boundary values of the reduced zeroth cohomology `H̃⁰ = componentConstant / ⟨1⟩` for the
`1`-skeleton of a finite complex:

* the **discrete** complex (empty graph `⊥`, no edges) has `H̃⁰` of dimension `card V − 1` — every
  vertex is its own component.  This is exactly the reduced-`H⁰` rank the isolated (fully discrete)
  Koszul family computes on the algebraic side in `KoszulCohomology.lean`
  (`n+1` classes for `n+2` vertices);
* a **connected** complex has `H̃⁰ = 0`.
-/

namespace GaloisForLFunctions

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] (F : Type*) [Field F]

/-- The discrete complex (empty graph) has one component per vertex. -/
theorem card_connectedComponent_bot :
    Fintype.card (ConnectedComponent (⊥ : SimpleGraph V)) = Fintype.card V := by
  refine Fintype.card_congr
    (Equiv.ofBijective (⊥ : SimpleGraph V).connectedComponentMk ⟨?_, ?_⟩).symm
  · intro u v h
    rwa [ConnectedComponent.eq, reachable_bot] at h
  · exact fun c => ConnectedComponent.ind (fun v => ⟨v, rfl⟩) c

/-- **Discrete-complex reduced `H⁰`.**  For the empty graph, reduced `H̃⁰` has dimension
`card V − 1` — matching the isolated Koszul `H¹`-rank on the algebraic side. -/
theorem finrank_reducedH0_bot [Nonempty V] :
    Module.finrank F
        (componentConstant (⊥ : SimpleGraph V) F ⧸
          (F ∙ (⟨fun _ => (1 : F), one_mem_componentConstant (⊥ : SimpleGraph V) F⟩ :
            componentConstant (⊥ : SimpleGraph V) F)))
      = Fintype.card V - 1 := by
  rw [finrank_reducedH0, card_connectedComponent_bot]

/-- **Connected-complex reduced `H⁰`.**  A connected complex has reduced `H̃⁰ = 0`. -/
theorem finrank_reducedH0_of_connected (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hG : G.Connected) :
    Module.finrank F
        (componentConstant G F ⧸
          (F ∙ (⟨fun _ => (1 : F), one_mem_componentConstant G F⟩ : componentConstant G F)))
      = 0 := by
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
  rw [finrank_reducedH0, hcard]

end

end GaloisForLFunctions
