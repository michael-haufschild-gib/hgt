import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Logic.Equiv.Basic

/-!
# Invariant restriction along an invariant map

If a map `π : Y → X` does not see a group action on `Y`, then every preimage `π ⁻¹' W` is stable
under that action.  Consequently the action restricts to `π ⁻¹' V`, the restricted map is again
invariant, and for `W ⊆ V` the `W`-part of `π ⁻¹' V` is equivariantly the same as `π ⁻¹' W`.

That is the reason the invariants of a pushforward restrict to an arithmetic open without moving
invariants past anything: the invariant sections over `W` are the same set whether computed on
the whole space or inside the restricted one.

* `deningerPreimageSub` is the preimage as a sub-action.
* `deningerRestrictInvariantMap` is invariance of the restricted map.
* `deningerPreimageRestrictEquiv` is the equivariant identification, and
  `deningerInvariantSectionsEquiv` is the resulting identification of invariant sections with
  values in an arbitrary coefficient `G`-set.
-/

namespace RHTower

section InvariantRestriction

variable {G Y X : Type*} [Monoid G] [MulAction G Y]

/-- A map is invariant when it does not see the action on its source. -/
def DeningerInvariantMap (G : Type*) [Monoid G] [MulAction G Y] (π : Y → X) : Prop :=
  ∀ (g : G) (y : Y), π (g • y) = π y

variable {π : Y → X}

/-- Preimages under an invariant map are stable under the action. -/
theorem deningerPreimage_smul_mem (hπ : DeningerInvariantMap G π) (W : Set X)
    (g : G) {y : Y} (hy : y ∈ π ⁻¹' W) : g • y ∈ π ⁻¹' W := by
  rw [Set.mem_preimage, hπ g y]
  exact hy

/-- The preimage of a set under an invariant map, as a sub-action. -/
def deningerPreimageSub (hπ : DeningerInvariantMap G π) (W : Set X) : SubMulAction G Y where
  carrier := π ⁻¹' W
  smul_mem' g _ hy := deningerPreimage_smul_mem hπ W g hy

@[simp] theorem deningerPreimageSub_carrier (hπ : DeningerInvariantMap G π) (W : Set X) :
    (deningerPreimageSub hπ W : Set Y) = π ⁻¹' W := rfl

@[simp] theorem deningerPreimageSub_mem (hπ : DeningerInvariantMap G π) (W : Set X) {y : Y} :
    y ∈ deningerPreimageSub hπ W ↔ π y ∈ W := Iff.rfl

/-- The map obtained by restricting `π` to a preimage. -/
def deningerRestrictMap (hπ : DeningerInvariantMap G π) (V : Set X) :
    ↥(deningerPreimageSub hπ V) → X := fun y => π y.1

/-- The restricted map is again invariant. -/
theorem deningerRestrictInvariantMap (hπ : DeningerInvariantMap G π) (V : Set X) :
    DeningerInvariantMap G (deningerRestrictMap hπ V) := fun g y => hπ g y.1

/-- **Invariant restriction, spaces.**  For `W ⊆ V`, the `W`-part of `π ⁻¹' V` is the same as
`π ⁻¹' W`. -/
def deningerPreimageRestrictEquiv (hπ : DeningerInvariantMap G π) {V W : Set X} (hW : W ⊆ V) :
    ↥(deningerPreimageSub (deningerRestrictInvariantMap hπ V) W) ≃
      ↥(deningerPreimageSub hπ W) where
  toFun y := ⟨y.1.1, y.2⟩
  invFun y := ⟨⟨y.1, hW y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem deningerPreimageRestrictEquiv_apply (hπ : DeningerInvariantMap G π)
    {V W : Set X} (hW : W ⊆ V)
    (y : ↥(deningerPreimageSub (deningerRestrictInvariantMap hπ V) W)) :
    ((deningerPreimageRestrictEquiv hπ hW y : ↥(deningerPreimageSub hπ W)) : Y) = y.1.1 := rfl

/-- The identification is equivariant. -/
theorem deningerPreimageRestrictEquiv_smul (hπ : DeningerInvariantMap G π)
    {V W : Set X} (hW : W ⊆ V) (g : G)
    (y : ↥(deningerPreimageSub (deningerRestrictInvariantMap hπ V) W)) :
    deningerPreimageRestrictEquiv hπ hW (g • y) = g • deningerPreimageRestrictEquiv hπ hW y :=
  rfl

/-- **Invariant restriction, sections.**  Equivariant sections with values in any coefficient
`G`-set are the same computed on `π ⁻¹' W` or inside `π ⁻¹' V`.  No invariants are moved past
any functor: the two invariant sets are in canonical bijection. -/
def deningerInvariantSectionsEquiv (hπ : DeningerInvariantMap G π) {V W : Set X} (hW : W ⊆ V)
    (M : Type*) [MulAction G M] :
    {s : ↥(deningerPreimageSub hπ W) → M // ∀ (g : G) (y), s (g • y) = g • s y} ≃
      {s : ↥(deningerPreimageSub (deningerRestrictInvariantMap hπ V) W) → M //
        ∀ (g : G) (y), s (g • y) = g • s y} where
  toFun s := ⟨fun y => s.1 (deningerPreimageRestrictEquiv hπ hW y), by
    intro g y
    show s.1 (deningerPreimageRestrictEquiv hπ hW (g • y))
        = g • s.1 (deningerPreimageRestrictEquiv hπ hW y)
    rw [deningerPreimageRestrictEquiv_smul, s.2]⟩
  invFun s := ⟨fun y => s.1 ((deningerPreimageRestrictEquiv hπ hW).symm y), by
    intro g y
    show s.1 ((deningerPreimageRestrictEquiv hπ hW).symm (g • y))
        = g • s.1 ((deningerPreimageRestrictEquiv hπ hW).symm y)
    rw [show (deningerPreimageRestrictEquiv hπ hW).symm (g • y)
        = g • (deningerPreimageRestrictEquiv hπ hW).symm y from rfl, s.2]⟩
  left_inv s := by
    apply Subtype.ext
    funext y
    rfl
  right_inv s := by
    apply Subtype.ext
    funext y
    rfl

end InvariantRestriction

end RHTower
