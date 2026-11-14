import GaloisForLFunctions.HTGeometry.BuildingAutomorphismAction
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Shears invisible to the two layers of a flag

A linear map `V/A → A` gives the automorphism `v ↦ v + f(v mod A)`.
Its displacement squares to zero, and it fixes both `A` and `V/A`
pointwise. More strongly, it fixes every subspace below or above `A`.
Consequently its quotient Steinberg action is trivial.

These are the explicit two-block unipotent symmetries behind the Levi
description of parabolic Steinberg modules in Ash--Gunnells,
arXiv:2611.03303, §2. The invariant-subspace criterion also describes
exactly which other subspaces a shear fixes.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Module

universe v u

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- A displacement factors from the quotient into the lower flag stage. -/
def flagShearDisplacement (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A) : V →ₗ[K] V :=
  A.subtype.comp (f.comp A.mkQ)

@[simp] theorem flagShearDisplacement_apply (A : Submodule K V)
    (f : (V ⧸ A) →ₗ[K] A) (x : V) :
    flagShearDisplacement A f x = (f (A.mkQ x) : V) := rfl

@[simp] theorem mkQ_flagShearDisplacement (A : Submodule K V)
    (f : (V ⧸ A) →ₗ[K] A) (x : V) :
    A.mkQ (flagShearDisplacement A f x) = 0 :=
  (Submodule.Quotient.mk_eq_zero A).mpr (f (A.mkQ x)).property

/-- Any two such displacements compose to zero, even with different parameters. -/
@[simp] theorem flagShearDisplacement_comp (A : Submodule K V)
    (f g : (V ⧸ A) →ₗ[K] A) (x : V) :
    flagShearDisplacement A f (flagShearDisplacement A g x) = 0 := by
  change ((f (A.mkQ (flagShearDisplacement A g x)) : A) : V) = 0
  rw [mkQ_flagShearDisplacement, map_zero]
  rfl

/-- The inverse of a shear is obtained by subtracting the same displacement. -/
def flagShear (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A) : V ≃ₗ[K] V where
  toLinearMap := LinearMap.id + flagShearDisplacement A f
  invFun x := x - flagShearDisplacement A f x
  left_inv x := by
    change (x + flagShearDisplacement A f x) -
      flagShearDisplacement A f (x + flagShearDisplacement A f x) = x
    rw [map_add, flagShearDisplacement_comp, add_zero, add_sub_cancel_right]
  right_inv x := by
    change (x - flagShearDisplacement A f x) +
      flagShearDisplacement A f (x - flagShearDisplacement A f x) = x
    rw [map_sub, flagShearDisplacement_comp, sub_zero, sub_add_cancel]

@[simp] theorem flagShear_apply (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A) (x : V) :
    flagShear A f x = x + flagShearDisplacement A f x := rfl

@[simp] theorem flagShear_symm_apply (A : Submodule K V)
    (f : (V ⧸ A) →ₗ[K] A) (x : V) :
    (flagShear A f).symm x = x - flagShearDisplacement A f x := rfl

/-- A shear acts as the identity on the quotient, without choosing a complement. -/
@[simp] theorem mkQ_flagShear (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A) (x : V) :
    A.mkQ (flagShear A f x) = A.mkQ x := by
  rw [flagShear_apply, map_add, mkQ_flagShearDisplacement, add_zero]

/-- The lower stage is fixed pointwise. -/
@[simp] theorem flagShear_on_submodule (A : Submodule K V)
    (f : (V ⧸ A) →ₗ[K] A) (x : A) : flagShear A f x = (x : V) := by
  have hx : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero A).mpr x.property
  rw [flagShear_apply, flagShearDisplacement_apply, hx, map_zero]
  exact add_zero _

/-- Shear parameters add under composition. -/
theorem flagShear_add (A : Submodule K V) (f g : (V ⧸ A) →ₗ[K] A) :
    flagShear A (f + g) = (flagShear A g).trans (flagShear A f) := by
  apply LinearEquiv.ext
  intro x
  change x + ((f + g) (A.mkQ x) : A) =
    (x + flagShearDisplacement A g x) +
      flagShearDisplacement A f (x + flagShearDisplacement A g x)
  rw [map_add, flagShearDisplacement_comp, add_zero]
  change x + ((f (A.mkQ x) : V) + (g (A.mkQ x) : V)) =
    (x + (g (A.mkQ x) : V)) + (f (A.mkQ x) : V)
  abel

/-- Different quotient-to-subspace maps give different automorphisms. -/
theorem flagShear_injective (A : Submodule K V) : Function.Injective (flagShear A) := by
  intro f g h
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := A.mkQ_surjective q
  apply Subtype.ext
  exact add_left_cancel (congrArg (fun e : V ≃ₗ[K] V => e x) h)

/-- A subspace is shear-invariant exactly when it contains its own displacements. -/
theorem flagShear_map_eq_iff (A U : Submodule K V) (f : (V ⧸ A) →ₗ[K] A) :
    U.map (flagShear A f).toLinearMap = U ↔
      ∀ x ∈ U, flagShearDisplacement A f x ∈ U := by
  constructor
  · intro h x hx
    have hfx : flagShear A f x ∈ U := by
      rw [← h]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    simpa only [flagShear_apply, add_sub_cancel_left] using U.sub_mem hfx hx
  · intro h
    apply le_antisymm
    · rintro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      exact U.add_mem hx (h x hx)
    · intro y hy
      refine Submodule.mem_map.mpr ⟨(flagShear A f).symm y, ?_,
        (flagShear A f).apply_symm_apply y⟩
      exact U.sub_mem hy (h y hy)

/-- Every subspace below the lower stage is fixed. -/
theorem flagShear_fixes_below (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A)
    (U : Set.Iic A) : U.val.map (flagShear A f).toLinearMap = U.val := by
  apply (flagShear_map_eq_iff A U.val f).mpr
  intro x hx
  have hxA : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero A).mpr (U.property hx)
  rw [flagShearDisplacement_apply, hxA, map_zero]
  exact U.val.zero_mem

/-- Every subspace above the lower stage is fixed. -/
theorem flagShear_fixes_above (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A)
    (U : Set.Ici A) : U.val.map (flagShear A f).toLinearMap = U.val :=
  (flagShear_map_eq_iff A U.val f).mpr (fun x _ => U.property (f (A.mkQ x)).property)

/-- The induced linear automorphism of the upper flag layer. -/
def flagShearQuotient (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A) :
    (V ⧸ A) ≃ₗ[K] (V ⧸ A) :=
  Submodule.Quotient.equiv A A (flagShear A f)
    (flagShear_fixes_above A f ⟨A, show A ≤ A from le_rfl⟩)

/-- The upper-layer automorphism is literally the identity. -/
theorem flagShearQuotient_eq_refl (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A) :
    flagShearQuotient A f = LinearEquiv.refl K (V ⧸ A) := by
  apply LinearEquiv.ext
  intro q
  obtain ⟨x, rfl⟩ := A.mkQ_surjective q
  exact mkQ_flagShear A f x

/-- The entire two-block unipotent radical is parametrized uniquely by `Hom(V/A,A)`:
fixing the lower stage and the quotient leaves exactly a shear. -/
theorem existsUnique_flagShear_iff (A : Submodule K V) (g : V ≃ₗ[K] V) :
    (∃! f : (V ⧸ A) →ₗ[K] A, flagShear A f = g) ↔
      (∀ x : A, g x = (x : V)) ∧ (∀ x : V, g x - x ∈ A) := by
  constructor
  · rintro ⟨f, rfl, _⟩
    refine ⟨flagShear_on_submodule A f, fun x => ?_⟩
    simpa only [flagShear_apply, add_sub_cancel_left] using (f (A.mkQ x)).property
  · rintro ⟨hA, hQ⟩
    let d : V →ₗ[K] A := (g.toLinearMap - LinearMap.id).codRestrict A hQ
    have hd : A ≤ LinearMap.ker d := by
      intro x hx
      change d x = 0
      apply Subtype.ext
      exact sub_eq_zero.mpr (hA ⟨x, hx⟩)
    let f : (V ⧸ A) →ₗ[K] A := A.liftQ d hd
    have hf : flagShear A f = g := by
      apply LinearEquiv.ext
      intro x
      change x + (d x : V) = g x
      change x + (g x - x) = g x
      abel
    exact ⟨f, hf, fun f' hf' => flagShear_injective A (hf'.trans hf.symm)⟩

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

/-- All these unipotent symmetries act trivially on the quotient Steinberg module. -/
theorem flagShear_steinbergAction (A : Submodule K V) (f : (V ⧸ A) →ₗ[K] A) (R : C) :
    steinbergAction K (V ⧸ A) R (flagShearQuotient A f) = 1 := by
  rw [flagShearQuotient_eq_refl]
  exact map_one _

end GaloisForLFunctions.HTGeometry
