import Mathlib

/-!
# Reduced zeroth cohomology of a finite complex is (components − 1)

The Hochster strand equivalence underlying facet-sewn Stanley–Reisner hypertranscendental realizations
matches each first Koszul class to a reduced simplicial cohomology class of an induced subcomplex.  On
the combinatorial side, the relevant target is the reduced zeroth cohomology `H̃⁰`, whose dimension is
`(number of connected components) − 1`.

This file formalizes that combinatorial target for the `1`-skeleton of a finite complex, presented as a
`SimpleGraph` on a finite vertex type over a field `F`:

* `componentConstant G F` — the `0`-cochains constant on connected components (`ker` of the graph
  coboundary), shown linearly equivalent to functions on the component set, so its dimension is the
  number of connected components;
* `finrank_reducedH0` — the reduced cohomology `H̃⁰ = componentConstant / ⟨1⟩` has dimension
  `card (components) − 1` (for a nonempty vertex set).

This is the discrete/`H⁰` layer of the general strand equivalence, matching the explicit Koszul
`H¹`-rank already computed for the isolated (fully discrete) family in `KoszulCohomology.lean`.
-/

namespace GaloisForLFunctions

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (F : Type*) [Field F]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Field F] in
/-- A `0`-cochain constant on adjacent vertices is constant on every connected component. -/
theorem eq_of_reachable_of_adj_invariant {f : V → F}
    (h : ∀ u v, G.Adj u v → f u = f v) {u v : V} (hr : G.Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj q ih => exact (h _ _ hadj).trans ih

/-- The submodule of `0`-cochains constant on connected components: the kernel of the graph
coboundary. -/
def componentConstant : Submodule F (V → F) where
  carrier := {f | ∀ u v, G.Adj u v → f u = f v}
  add_mem' := fun ha hb u v huv => by
    simp only [Pi.add_apply]; rw [ha u v huv, hb u v huv]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c f hf u v huv => by
    simp only [Pi.smul_apply]; rw [hf u v huv]

/-- Component-constant `0`-cochains are exactly the functions on the connected-component set. -/
def componentConstantEquiv : componentConstant G F ≃ₗ[F] (G.ConnectedComponent → F) where
  toFun f := ConnectedComponent.lift f.1
    (fun v w p _ => eq_of_reachable_of_adj_invariant G F f.2 ⟨p⟩)
  map_add' f g := by
    ext c
    induction c using ConnectedComponent.ind with
    | _ v => simp
  map_smul' r f := by
    ext c
    induction c using ConnectedComponent.ind with
    | _ v => simp
  invFun g := ⟨fun v => g (G.connectedComponentMk v),
    fun u v huv => congrArg g (ConnectedComponent.sound huv.reachable)⟩
  left_inv f := by
    apply Subtype.ext; funext v; simp
  right_inv g := by
    ext c
    induction c using ConnectedComponent.ind with
    | _ v => simp

/-- **The kernel of the graph coboundary has dimension equal to the number of connected
components.** -/
theorem finrank_componentConstant :
    Module.finrank F (componentConstant G F) = Fintype.card G.ConnectedComponent := by
  rw [(componentConstantEquiv G F).finrank_eq]
  exact Module.finrank_pi F

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The all-ones `0`-cochain is component-constant. -/
theorem one_mem_componentConstant : (fun _ => (1 : F)) ∈ componentConstant G F :=
  fun _ _ _ => rfl

/-- **Reduced zeroth cohomology has dimension (components − 1).**  Over a nonempty vertex set, the
reduced cohomology `H̃⁰ = componentConstant / ⟨1⟩` has dimension `card (components) − 1`. -/
theorem finrank_reducedH0 [Nonempty V] :
    Module.finrank F
        (componentConstant G F ⧸
          (F ∙ (⟨fun _ => (1 : F), one_mem_componentConstant G F⟩ : componentConstant G F)))
      = Fintype.card G.ConnectedComponent - 1 := by
  have hone : (⟨fun _ => (1 : F), one_mem_componentConstant G F⟩ : componentConstant G F) ≠ 0 := by
    intro h
    have := congrArg (fun x => ((x : componentConstant G F) : V → F) (Classical.arbitrary V)) h
    simp at this
  have hspan : Module.finrank F
      (F ∙ (⟨fun _ => (1 : F), one_mem_componentConstant G F⟩ : componentConstant G F)) = 1 :=
    finrank_span_singleton hone
  have hq := Submodule.finrank_quotient_add_finrank
    (F ∙ (⟨fun _ => (1 : F), one_mem_componentConstant G F⟩ : componentConstant G F))
  rw [hspan, finrank_componentConstant] at hq
  omega

end

end GaloisForLFunctions
