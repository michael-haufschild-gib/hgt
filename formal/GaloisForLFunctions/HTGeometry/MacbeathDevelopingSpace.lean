import GaloisForLFunctions.HTGeometry.MacbeathPresentation

/-!
# The developing space of Macbeath's construction

Macbeath's theorem is proved by developing the fundamental open set `V` along the presented group:
one takes a disjoint copy of `V` for every element of `MacbeathGroup V` and glues the copy at `g` to
the copy at `g · s_γ` along the overlap `V ∩ γ·V`.  The resulting space maps to `X`, and the map is
a covering; simple connectivity of `X` then forces it to be injective, which is exactly the
injectivity of `macbeathHom`.

This file builds the space, the gluing relation, the map to `X`, and its continuity and
surjectivity.

* `DevRel`, `DevSpace` : the elementary moves and the developed space.
* `devMap` : **the map to `X`**, continuous and surjective.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- A sheet of the developing space: an element of Macbeath's group together with a point of `V`. -/
abbrev DevSheet (V : Set X) : Type _ := Σ _ : MacbeathGroup (G := G) V, V

/-- The elementary gluing move: the copy of `V` at `g` is glued to the copy at `g · s_γ` along the
overlap, by `x ↦ γ⁻¹ · x`. -/
inductive DevRel (V : Set X) : DevSheet (G := G) V → DevSheet (G := G) V → Prop
  | move (g : MacbeathGroup (G := G) V) (γ : meetSet (G := G) V) (x y : V)
      (h : (y : X) = ((γ : G))⁻¹ • (x : X)) :
      DevRel V ⟨g, x⟩ ⟨g * macbeathOf V γ, y⟩

/-- **The developed space.** -/
abbrev DevSpace (V : Set X) : Type _ := Quot (DevRel (G := G) V)

/-- The map from a sheet to `X`. -/
def devSheetMap (V : Set X) (p : DevSheet (G := G) V) : X :=
  macbeathHom V p.1 • (p.2 : X)

theorem devSheetMap_respects (V : Set X) {p q : DevSheet (G := G) V} (h : DevRel V p q) :
    devSheetMap V p = devSheetMap V q := by
  cases h with
  | move g γ x y hxy =>
      show macbeathHom V g • (x : X) = macbeathHom V (g * macbeathOf V γ) • (y : X)
      rw [map_mul, macbeathHom_of, hxy, mul_smul, smul_inv_smul]

/-- **The map from the developed space to `X`.** -/
def devMap (V : Set X) : DevSpace (G := G) V → X :=
  Quot.lift (devSheetMap V) (fun _ _ h => devSheetMap_respects V h)

@[simp]
theorem devMap_mk (V : Set X) (p : DevSheet (G := G) V) :
    devMap V (Quot.mk _ p) = macbeathHom V p.1 • (p.2 : X) := rfl

theorem continuous_devSheetMap (V : Set X) : Continuous (devSheetMap (G := G) V) := by
  refine continuous_sigma ?_
  intro g
  exact (continuous_const_smul (macbeathHom V g)).comp continuous_subtype_val

theorem continuous_devMap (V : Set X) : Continuous (devMap (G := G) V) :=
  continuous_quot_lift _ (continuous_devSheetMap V)

theorem devMap_surjective {V : Set X} (hcover : ⋃ g : G, g • V = (univ : Set X))
    [ConnectedSpace X] (hVopen : IsOpen V) (hVne : V.Nonempty) :
    Function.Surjective (devMap (G := G) V) := by
  intro x
  have hx : x ∈ ⋃ g : G, g • V := by rw [hcover]; trivial
  obtain ⟨g, hg⟩ := mem_iUnion.1 hx
  obtain ⟨v, hv, rfl⟩ := hg
  obtain ⟨gt, hgt⟩ := macbeathHom_surjective hVopen hVne hcover g
  exact ⟨Quot.mk _ ⟨gt, ⟨v, hv⟩⟩, by rw [devMap_mk, hgt]⟩

end GaloisForLFunctions.HTGeometry
