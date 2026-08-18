import Mathlib.Topology.Homotopy.Lifting

/-!
# A covering of a simply connected space is trivial

Over a simply connected, locally path-connected base a covering map with connected total space is
injective: the identity of the base lifts to a section, and the section composed with the covering
map is a lift of the covering map through itself agreeing with the identity at a point, hence is the
identity.

This is the topological input of Macbeath's presentation theorem — the step where simple
connectivity of the space acted on forces the developing covering to be trivial, so that the group
presented by the overlaps of a fundamental open set is the group itself.

* `isCoveringMap_injective_of_simplyConnected` : **the covering is injective.**
-/

namespace GaloisForLFunctions.HTGeometry

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- **A covering map onto a simply connected, locally path-connected base, with connected total
space, is injective.** -/
theorem isCoveringMap_injective_of_simplyConnected [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [PreconnectedSpace E] (hp : IsCoveringMap p) (e₀ : E) :
    Function.Injective p := by
  obtain ⟨s, ⟨hs₀, hs⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) (p e₀) e₀ rfl
  have hcomp : (s : X → E) ∘ p = id := by
    refine hp.eq_of_comp_eq (g₁ := (s : X → E) ∘ p) (g₂ := id)
      (s.continuous.comp hp.continuous) continuous_id ?_ e₀ ?_
    · funext e
      show p (s (p e)) = p e
      have := congrFun hs (p e)
      simpa using this
    · show s (p e₀) = e₀
      exact hs₀
  intro a b hab
  have ha : s (p a) = a := congrFun hcomp a
  have hb : s (p b) = b := congrFun hcomp b
  rw [← ha, ← hb, hab]

end GaloisForLFunctions.HTGeometry
