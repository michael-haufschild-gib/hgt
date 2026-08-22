/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEquality

/-!
# Hasse detection of algebra-homomorphism equality

Equality of fixed global algebra homomorphisms is reflected by scalar extension.  Consequently,
agreement of their completed scalar extensions at every place certifies their global equality.
This is an equality theorem for globally specified maps; it does not assert that independently
chosen local homomorphisms descend to a global homomorphism.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x y

/-- Scalar extension of an algebra homomorphism along a field extension. -/
def algHomBaseChange {K : Type u} {L : Type v} {A : Type w} {B : Type x}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f : A →ₐ[K] B) : L ⊗[K] A →ₐ[L] L ⊗[K] B :=
  Algebra.TensorProduct.map (AlgHom.id L L) f

/-- Injectivity of an algebra homomorphism is reflected by every field scalar extension. -/
theorem algHom_injective_iff_baseChange_injective {K : Type u} {L : Type v} {A : Type w}
    {B : Type x} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
    [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Injective f ↔ Function.Injective (algHomBaseChange (L := L) f) := by
  change Function.Injective f.toLinearMap ↔
    Function.Injective (algHomBaseChange (L := L) f).toLinearMap
  change Function.Injective f.toLinearMap ↔ Function.Injective (f.toLinearMap.baseChange L)
  exact linearMap_injective_iff_baseChange_injective (L := L) f.toLinearMap

/-- Surjectivity of an algebra homomorphism is reflected by every field scalar extension. -/
theorem algHom_surjective_iff_baseChange_surjective {K : Type u} {L : Type v} {A : Type w}
    {B : Type x} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
    [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Surjective f ↔ Function.Surjective (algHomBaseChange (L := L) f) := by
  change Function.Surjective f.toLinearMap ↔
    Function.Surjective (algHomBaseChange (L := L) f).toLinearMap
  change Function.Surjective f.toLinearMap ↔ Function.Surjective (f.toLinearMap.baseChange L)
  exact linearMap_surjective_iff_baseChange_surjective (L := L) f.toLinearMap

/-- Bijectivity of an algebra homomorphism is reflected by every field scalar extension. -/
theorem algHom_bijective_iff_baseChange_bijective {K : Type u} {L : Type v} {A : Type w}
    {B : Type x} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
    [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Bijective f ↔ Function.Bijective (algHomBaseChange (L := L) f) := by
  change Function.Bijective f.toLinearMap ↔
    Function.Bijective (algHomBaseChange (L := L) f).toLinearMap
  change Function.Bijective f.toLinearMap ↔ Function.Bijective (f.toLinearMap.baseChange L)
  exact linearMap_bijective_iff_baseChange_bijective (L := L) f.toLinearMap

/-- Two algebra homomorphisms are equal exactly when their scalar extensions are equal. -/
theorem algHom_eq_iff_baseChange_eq {K : Type u} {L : Type v} {A : Type w} {B : Type x}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f g : A →ₐ[K] B) :
    f = g ↔ algHomBaseChange (L := L) f = algHomBaseChange (L := L) g := by
  constructor
  · intro h
    exact congrArg (algHomBaseChange (L := L)) h
  · intro h
    ext a
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) B
    have happly := DFunLike.congr_fun h ((1 : L) ⊗ₜ[K] a)
    change (1 : L) ⊗ₜ[K] f a = 1 ⊗ₜ[K] g a at happly
    exact happly

/-- Scalar extension commutes with composition of algebra homomorphisms. -/
theorem algHomBaseChange_comp {K : Type u} {L : Type v} {A : Type w} {B : Type x} {C : Type y}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [Ring C] [Algebra K C] (g : B →ₐ[K] C) (f : A →ₐ[K] B) :
    algHomBaseChange (L := L) (g.comp f) =
      (algHomBaseChange (L := L) g).comp (algHomBaseChange (L := L) f) := by
  exact Algebra.TensorProduct.map_comp (AlgHom.id L L) (AlgHom.id L L) g f

/-- A fixed algebraic commutative diagram commutes exactly when its scalar extension does. -/
theorem algHom_comp_eq_iff_baseChange_comp_eq
    {K : Type u} {L : Type v} {A : Type w} {B : Type x} {C : Type y}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [Ring C] [Algebra K C] (f : A →ₐ[K] B) (g : B →ₐ[K] C) (h : A →ₐ[K] C) :
    g.comp f = h ↔ (algHomBaseChange (L := L) g).comp (algHomBaseChange (L := L) f) =
      algHomBaseChange (L := L) h := by
  rw [← algHomBaseChange_comp]
  exact algHom_eq_iff_baseChange_eq (L := L) (g.comp f) h

/-- Scalar extension of an algebra equivalence along a field extension. -/
def algEquivBaseChange {K : Type u} {L : Type v} {A : Type w} {B : Type x}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (e : A ≃ₐ[K] B) : (L ⊗[K] A) ≃ₐ[L] (L ⊗[K] B) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl) e

/-- Two algebra equivalences are equal exactly when their scalar extensions are equal. -/
theorem algEquiv_eq_iff_baseChange_eq {K : Type u} {L : Type v} {A : Type w} {B : Type x}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (e f : A ≃ₐ[K] B) :
    e = f ↔ algEquivBaseChange (L := L) e = algEquivBaseChange (L := L) f := by
  constructor
  · intro h
    exact congrArg (algEquivBaseChange (L := L)) h
  · intro h
    apply AlgEquiv.coe_toAlgHom_injective
    apply (algHom_eq_iff_baseChange_eq (L := L) e.toAlgHom f.toAlgHom).mpr
    have hh := congrArg AlgEquiv.toAlgHom h
    change algHomBaseChange (L := L) e.toAlgHom = algHomBaseChange (L := L) f.toAlgHom at hh
    exact hh

/-- Two algebra homomorphisms over a number field are equal exactly when all of their completed
scalar extensions are equal. -/
theorem numberField_algHom_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f g : A →ₐ[K] B) :
    f = g ↔ ∀ p : NumberFieldPlace K,
      algHomBaseChange (L := completion K p) f = algHomBaseChange (L := completion K p) g := by
  constructor
  · intro h p
    exact (algHom_eq_iff_baseChange_eq (L := completion K p) f g).mp h
  · intro h
    exact (algHom_eq_iff_baseChange_eq
      (L := completion K (witnessPlace K)) f g).mpr (h (witnessPlace K))

/-- A fixed algebraic diagram over a number field commutes exactly when all of its completed
scalar extensions commute. -/
theorem numberField_algHom_comp_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w} {C : Type x}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] [Ring C] [Algebra K C]
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) (h : A →ₐ[K] C) :
    g.comp f = h ↔ ∀ p : NumberFieldPlace K,
      (algHomBaseChange (L := completion K p) g).comp
          (algHomBaseChange (L := completion K p) f) =
        algHomBaseChange (L := completion K p) h := by
  constructor
  · intro hcomp p
    exact (algHom_comp_eq_iff_baseChange_comp_eq (L := completion K p) f g h).mp hcomp
  · intro hcomp
    exact (algHom_comp_eq_iff_baseChange_comp_eq
      (L := completion K (witnessPlace K)) f g h).mpr (hcomp (witnessPlace K))

/-- Two algebra equivalences over a number field are equal exactly when their completed scalar
extensions are equal at every place. -/
theorem numberField_algEquiv_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (e f : A ≃ₐ[K] B) :
    e = f ↔ ∀ p : NumberFieldPlace K,
      algEquivBaseChange (L := completion K p) e = algEquivBaseChange (L := completion K p) f := by
  constructor
  · intro h p
    exact (algEquiv_eq_iff_baseChange_eq (L := completion K p) e f).mp h
  · intro h
    exact (algEquiv_eq_iff_baseChange_eq
      (L := completion K (witnessPlace K)) e f).mpr (h (witnessPlace K))

/-- Two algebra homomorphisms over `F(t)` are equal exactly when all of their finite and infinite
completed scalar extensions are equal. -/
theorem rationalFunction_algHom_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f g : A →ₐ[RatFunc F] B) :
    f = g ↔ ∀ p : RationalFunctionPlace F,
      algHomBaseChange (L := rationalFunctionCompletion F p) f =
        algHomBaseChange (L := rationalFunctionCompletion F p) g := by
  constructor
  · intro h p
    exact (algHom_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) f g).mp h
  · intro h
    exact (algHom_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F .infinite) f g).mpr (h .infinite)

/-- A fixed algebraic diagram over `F(t)` commutes exactly when all of its finite and infinite
completed scalar extensions commute. -/
theorem rationalFunction_algHom_comp_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w} {C : Type x}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    [Ring C] [Algebra (RatFunc F) C]
    (f : A →ₐ[RatFunc F] B) (g : B →ₐ[RatFunc F] C) (h : A →ₐ[RatFunc F] C) :
    g.comp f = h ↔ ∀ p : RationalFunctionPlace F,
      (algHomBaseChange (L := rationalFunctionCompletion F p) g).comp
          (algHomBaseChange (L := rationalFunctionCompletion F p) f) =
        algHomBaseChange (L := rationalFunctionCompletion F p) h := by
  constructor
  · intro hcomp p
    exact (algHom_comp_eq_iff_baseChange_comp_eq
      (L := rationalFunctionCompletion F p) f g h).mp hcomp
  · intro hcomp
    exact (algHom_comp_eq_iff_baseChange_comp_eq
      (L := rationalFunctionCompletion F .infinite) f g h).mpr (hcomp .infinite)

/-- Two algebra equivalences over `F(t)` are equal exactly when their finite and infinite
completed scalar extensions are equal. -/
theorem rationalFunction_algEquiv_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (e f : A ≃ₐ[RatFunc F] B) :
    e = f ↔ ∀ p : RationalFunctionPlace F,
      algEquivBaseChange (L := rationalFunctionCompletion F p) e =
        algEquivBaseChange (L := rationalFunctionCompletion F p) f := by
  constructor
  · intro h p
    exact (algEquiv_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) e f).mp h
  · intro h
    exact (algEquiv_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F .infinite) e f).mpr (h .infinite)

/-- An algebra homomorphism over a number field is injective exactly when all of its completed
scalar extensions are injective. -/
theorem numberField_algHom_injective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Injective f ↔ ∀ p : NumberFieldPlace K,
      Function.Injective (algHomBaseChange (L := completion K p) f) := by
  constructor
  · intro h p
    exact (algHom_injective_iff_baseChange_injective (L := completion K p) f).mp h
  · intro h
    exact (algHom_injective_iff_baseChange_injective
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- An algebra homomorphism over a number field is surjective exactly when all of its completed
scalar extensions are surjective. -/
theorem numberField_algHom_surjective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Surjective f ↔ ∀ p : NumberFieldPlace K,
      Function.Surjective (algHomBaseChange (L := completion K p) f) := by
  constructor
  · intro h p
    exact (algHom_surjective_iff_baseChange_surjective (L := completion K p) f).mp h
  · intro h
    exact (algHom_surjective_iff_baseChange_surjective
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- An algebra homomorphism over a number field is bijective exactly when all of its completed
scalar extensions are bijective. -/
theorem numberField_algHom_bijective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Bijective f ↔ ∀ p : NumberFieldPlace K,
      Function.Bijective (algHomBaseChange (L := completion K p) f) := by
  constructor
  · intro h p
    exact (algHom_bijective_iff_baseChange_bijective (L := completion K p) f).mp h
  · intro h
    exact (algHom_bijective_iff_baseChange_bijective
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- An algebra homomorphism over `F(t)` is injective exactly when all finite and infinite
completed scalar extensions are injective. -/
theorem rationalFunction_algHom_injective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    Function.Injective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Injective (algHomBaseChange (L := rationalFunctionCompletion F p) f) := by
  constructor
  · intro h p
    exact (algHom_injective_iff_baseChange_injective
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (algHom_injective_iff_baseChange_injective
      (L := rationalFunctionCompletion F .infinite) f).mpr (h .infinite)

/-- An algebra homomorphism over `F(t)` is surjective exactly when all finite and infinite
completed scalar extensions are surjective. -/
theorem rationalFunction_algHom_surjective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    Function.Surjective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Surjective (algHomBaseChange (L := rationalFunctionCompletion F p) f) := by
  constructor
  · intro h p
    exact (algHom_surjective_iff_baseChange_surjective
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (algHom_surjective_iff_baseChange_surjective
      (L := rationalFunctionCompletion F .infinite) f).mpr (h .infinite)

/-- An algebra homomorphism over `F(t)` is bijective exactly when all finite and infinite
completed scalar extensions are bijective. -/
theorem rationalFunction_algHom_bijective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    Function.Bijective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Bijective (algHomBaseChange (L := rationalFunctionCompletion F p) f) := by
  constructor
  · intro h p
    exact (algHom_bijective_iff_baseChange_bijective
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (algHom_bijective_iff_baseChange_bijective
      (L := rationalFunctionCompletion F .infinite) f).mpr (h .infinite)

/-- Injectivity of an algebra homomorphism over a number field is detected at one completion. -/
theorem numberField_algHom_injective_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Injective f ↔ ∃ p : NumberFieldPlace K,
      Function.Injective (algHomBaseChange (L := completion K p) f) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algHom_injective_iff_baseChange_injective (L := completion K (witnessPlace K)) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algHom_injective_iff_baseChange_injective (L := completion K p) f).mpr hp

/-- Surjectivity of an algebra homomorphism over a number field is detected at one completion. -/
theorem numberField_algHom_surjective_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Surjective f ↔ ∃ p : NumberFieldPlace K,
      Function.Surjective (algHomBaseChange (L := completion K p) f) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algHom_surjective_iff_baseChange_surjective (L := completion K (witnessPlace K)) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algHom_surjective_iff_baseChange_surjective (L := completion K p) f).mpr hp

/-- Bijectivity of an algebra homomorphism over a number field is detected at one completion. -/
theorem numberField_algHom_bijective_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    Function.Bijective f ↔ ∃ p : NumberFieldPlace K,
      Function.Bijective (algHomBaseChange (L := completion K p) f) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algHom_bijective_iff_baseChange_bijective (L := completion K (witnessPlace K)) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algHom_bijective_iff_baseChange_bijective (L := completion K p) f).mpr hp

/-- Injectivity of an algebra homomorphism over a rational function field is detected at one
finite or infinite completion. -/
theorem rationalFunction_algHom_injective_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    Function.Injective f ↔ ∃ p : RationalFunctionPlace F,
      Function.Injective (algHomBaseChange (L := rationalFunctionCompletion F p) f) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algHom_injective_iff_baseChange_injective
        (L := rationalFunctionCompletion F .infinite) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algHom_injective_iff_baseChange_injective
      (L := rationalFunctionCompletion F p) f).mpr hp

/-- Surjectivity of an algebra homomorphism over a rational function field is detected at one
finite or infinite completion. -/
theorem rationalFunction_algHom_surjective_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    Function.Surjective f ↔ ∃ p : RationalFunctionPlace F,
      Function.Surjective (algHomBaseChange (L := rationalFunctionCompletion F p) f) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algHom_surjective_iff_baseChange_surjective
        (L := rationalFunctionCompletion F .infinite) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algHom_surjective_iff_baseChange_surjective
      (L := rationalFunctionCompletion F p) f).mpr hp

/-- Bijectivity of an algebra homomorphism over a rational function field is detected at one
finite or infinite completion. -/
theorem rationalFunction_algHom_bijective_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    Function.Bijective f ↔ ∃ p : RationalFunctionPlace F,
      Function.Bijective (algHomBaseChange (L := rationalFunctionCompletion F p) f) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algHom_bijective_iff_baseChange_bijective
        (L := rationalFunctionCompletion F .infinite) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algHom_bijective_iff_baseChange_bijective
      (L := rationalFunctionCompletion F p) f).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
