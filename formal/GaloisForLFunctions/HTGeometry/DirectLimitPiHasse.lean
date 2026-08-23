import GaloisForLFunctions.HTGeometry.DirectLimitPi

/-!
# Hasse assembly for finite products of filtered colimits

Filtered colimits commute with finite products of modules.  Pointwise component data therefore
detect a global product-limit class, and every finite compatible family of component-limit classes
has one unique global realization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w r

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [DecidableEq ι]
  {ρ : Type r} [Fintype ρ]
  {G : ρ → ι → Type w} [∀ p i, AddCommGroup (G p i)] [∀ p i, Module R (G p i)]
  (f : ∀ (p : ρ) (i j : ι), i ≤ j → G p i →ₗ[R] G p j)
  [IsDirectedOrder ι] [Nonempty ι]
  [∀ p, DirectedSystem (G p) fun i j h => f p i j h]

/-- Two classes in a filtered colimit of finite products agree exactly when every component-limit
coordinate agrees. -/
theorem directLimitPi_congr_hasse_iff
    (x y : Module.DirectLimit (fun i => ∀ p, G p i) (piTransition f)) :
    (∀ p, directLimitPiMap f x p = directLimitPiMap f y p) ↔ x = y := by
  constructor
  · intro h
    apply directLimitPiMap_injective f
    funext p
    exact h p
  · rintro rfl p
    rfl

/-- Every finite family of component-limit classes has one unique global class in the filtered
colimit of products. -/
theorem directLimitPi_existsUnique_hasse
    (ξ : ∀ p, Module.DirectLimit (G p) (f p)) :
    ∃! x : Module.DirectLimit (fun i => ∀ p, G p i) (piTransition f),
      ∀ p, directLimitPiMap f x p = ξ p := by
  obtain ⟨x, hx⟩ := directLimitPiMap_surjective f ξ
  refine ⟨x, fun p => congrFun hx p, ?_⟩
  intro y hy
  apply directLimitPiMap_injective f
  funext p
  exact (hy p).trans (congrFun hx p).symm

end


end GaloisForLFunctions.HTGeometry
