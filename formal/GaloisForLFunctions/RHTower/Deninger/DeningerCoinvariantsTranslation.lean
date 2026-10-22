import GaloisForLFunctions.RHTower.Deninger.DeningerLESMono

/-!
# Translation by a central element on coinvariants

In an abelian group every translation of a representation is a morphism of representations, and on
coinvariants it is the identity.  So the boundary map of the two term resolution of the trivial
representation, which is translation by the generator minus the identity, dies on coinvariants.

* `deningerRhoHom` : translation as a morphism of representations.
* `deningerCoinvariants_rhoHom` : it is the identity on coinvariants.
-/

namespace RHTower

open CategoryTheory Rep Representation

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Translation by an element of an abelian group, as a morphism of representations. -/
noncomputable def deningerRhoHom (hcomm : ∀ a b : G, a * b = b * a) (M : Rep k G) (g : G) :
    M ⟶ M :=
  Rep.ofHom ⟨M.ρ g, fun h => by
    rw [show M.ρ g ∘ₗ M.ρ h = M.ρ (g * h) from (map_mul M.ρ g h).symm,
      show M.ρ h ∘ₗ M.ρ g = M.ρ (h * g) from (map_mul M.ρ h g).symm, hcomm]⟩

@[simp] theorem deningerRhoHom_hom (hcomm : ∀ a b : G, a * b = b * a) (M : Rep k G) (g : G)
    (x : M.V) : (deningerRhoHom hcomm M g).hom x = M.ρ g x := rfl

/-- **Translation is the identity on coinvariants.** -/
theorem deningerCoinvariants_rhoHom (hcomm : ∀ a b : G, a * b = b * a) (M : Rep k G) (g : G) :
    (Rep.coinvariantsFunctor k G).map (deningerRhoHom hcomm M g) = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  induction x using Representation.Coinvariants.induction_on with
  | h y =>
    show Representation.Coinvariants.map _ _ (deningerRhoHom hcomm M g).hom
      (Representation.Coinvariants.mk M.ρ y) = _
    rw [Representation.Coinvariants.map_mk]
    show Representation.Coinvariants.mk M.ρ (M.ρ g y) = _
    rw [Representation.Coinvariants.mk_self_apply]
    rfl

end RHTower
