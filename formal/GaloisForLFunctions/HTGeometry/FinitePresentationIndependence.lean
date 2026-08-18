import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Finiteness

/-!
# Finite presentability does not depend on the chosen free presentation

If a group is the quotient of one finitely generated free group by the normal closure of a *finite*
set of relators, the same is true for **every** surjection from a finitely generated free group.
The proof lifts the two presentations through each other: `α : F₁ → F₂` and `β : F₂ → F₁` over the
identity of `G`, and the relators of the second presentation are the images `α(S₁)` together with
the finitely many words `α(β(x))·x⁻¹` recording that `α ∘ β` is the identity on generators.

* `map_normalClosure_le` : a homomorphism carries a normal closure into the normal closure of the
  image.
* `exists_finite_relators` : **the independence statement.**
-/

namespace GaloisForLFunctions.HTGeometry

open Subgroup

/-- A homomorphism carries a normal closure into the normal closure of the image. -/
theorem map_normalClosure_le {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Set G) :
    Subgroup.map f (normalClosure S) ≤ normalClosure (f '' S) := by
  have hmap : Subgroup.map f (closure (Group.conjugatesOfSet S))
      = closure (f '' Group.conjugatesOfSet S) := MonoidHom.map_closure f _
  refine le_trans (le_of_eq hmap) ((closure_le _).2 ?_)
  rintro _ ⟨y, hy, rfl⟩
  rw [Group.mem_conjugatesOfSet_iff] at hy
  obtain ⟨s, hs, hconj⟩ := hy
  obtain ⟨x, rfl⟩ := isConj_iff.mp hconj
  have : f (x * s * x⁻¹) = f x * f s * (f x)⁻¹ := by simp
  rw [this]
  exact Subgroup.subset_closure (Group.mem_conjugatesOfSet_iff.2
    ⟨f s, Set.mem_image_of_mem f hs, isConj_iff.2 ⟨f x, rfl⟩⟩)

/-- The core of the independence statement, with the relators supplied abstractly. -/
theorem ker_eq_normalClosure_of_lifts {X₁ X₂ : Type*} {G : Type*} [Group G]
    (ψ₁ : FreeGroup X₁ →* G) (ψ₂ : FreeGroup X₂ →* G)
    (α : FreeGroup X₁ →* FreeGroup X₂) (β : FreeGroup X₂ →* FreeGroup X₁)
    (hβ : ∀ w, ψ₁ (β w) = ψ₂ w)
    {S₁ : Set (FreeGroup X₁)} (hker₁ : ψ₁.ker = normalClosure S₁)
    {S₂ : Set (FreeGroup X₂)}
    (hgen : ∀ x : X₂, (α (β (FreeGroup.of x)))⁻¹ * FreeGroup.of x ∈ S₂)
    (himg : α '' S₁ ⊆ S₂) (hsub : S₂ ⊆ (ψ₂.ker : Set (FreeGroup X₂))) :
    ψ₂.ker = normalClosure S₂ := by
  refine le_antisymm ?_ (normalClosure_le_normal hsub)
  have hmk : ∀ x : X₂, (QuotientGroup.mk' (normalClosure S₂)) (α (β (FreeGroup.of x)))
      = (QuotientGroup.mk' (normalClosure S₂)) (FreeGroup.of x) := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact subset_normalClosure (hgen x)
  have hcomp := FreeGroup.ext_hom
    ((QuotientGroup.mk' (normalClosure S₂)).comp (α.comp β))
    (QuotientGroup.mk' (normalClosure S₂)) hmk
  intro w hw
  have hβw : β w ∈ ψ₁.ker := by
    rw [MonoidHom.mem_ker, hβ w]
    exact MonoidHom.mem_ker.1 hw
  have hαβw : α (β w) ∈ normalClosure S₂ := by
    have h1 : α (β w) ∈ Subgroup.map α (normalClosure S₁) := ⟨β w, hker₁ ▸ hβw, rfl⟩
    exact normalClosure_le_normal (le_trans himg subset_normalClosure)
      (map_normalClosure_le α S₁ h1)
  have hq := congrArg (fun f : FreeGroup X₂ →* FreeGroup X₂ ⧸ normalClosure S₂ => f w) hcomp
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hq
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hq, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact hαβw

/-- **Finite presentability is a property of the group, not of the presentation.**  If `G` is the
quotient of a finitely generated free group by the normal closure of a finite set, then the kernel
of every surjection onto `G` from a finitely generated free group is again the normal closure of a
finite set. -/
theorem exists_finite_relators {X₁ X₂ : Type*} [Finite X₁] [Finite X₂] {G : Type*} [Group G]
    (ψ₁ : FreeGroup X₁ →* G) (ψ₂ : FreeGroup X₂ →* G)
    (hψ₁ : Function.Surjective ψ₁) (hψ₂ : Function.Surjective ψ₂)
    {S₁ : Set (FreeGroup X₁)} (hS₁ : S₁.Finite) (hker₁ : ψ₁.ker = normalClosure S₁) :
    ∃ S₂ : Set (FreeGroup X₂), S₂.Finite ∧ ψ₂.ker = normalClosure S₂ := by
  classical
  choose a ha using fun x : X₁ => hψ₂ (ψ₁ (FreeGroup.of x))
  choose b hb using fun x : X₂ => hψ₁ (ψ₂ (FreeGroup.of x))
  obtain ⟨α, hα⟩ : ∃ α : FreeGroup X₁ →* FreeGroup X₂, ∀ w, ψ₂ (α w) = ψ₁ w := by
    refine ⟨FreeGroup.lift a, fun w => ?_⟩
    have : ψ₂.comp (FreeGroup.lift a) = ψ₁ :=
      FreeGroup.ext_hom _ _ fun x => by simpa using ha x
    exact congrArg (fun f : FreeGroup X₁ →* G => f w) this
  obtain ⟨β, hβ⟩ : ∃ β : FreeGroup X₂ →* FreeGroup X₁, ∀ w, ψ₁ (β w) = ψ₂ w := by
    refine ⟨FreeGroup.lift b, fun w => ?_⟩
    have : ψ₁.comp (FreeGroup.lift b) = ψ₂ :=
      FreeGroup.ext_hom _ _ fun x => by simpa using hb x
    exact congrArg (fun f : FreeGroup X₂ →* G => f w) this
  refine ⟨(α '' S₁) ∪ Set.range (fun x : X₂ => (α (β (FreeGroup.of x)))⁻¹ * FreeGroup.of x),
    (hS₁.image _).union (Set.finite_range _),
    ker_eq_normalClosure_of_lifts ψ₁ ψ₂ α β hβ hker₁ (fun x => Or.inr ⟨x, rfl⟩)
      Set.subset_union_left ?_⟩
  rintro w (⟨s, hs, rfl⟩ | ⟨x, rfl⟩)
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, hα s]
    exact MonoidHom.mem_ker.1 (hker₁ ▸ subset_normalClosure hs)
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hα, hβ, inv_mul_cancel]

end GaloisForLFunctions.HTGeometry
