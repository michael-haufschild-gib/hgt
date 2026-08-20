/-
Copyright (c) 2025 Matthew Jasper, Kevin Buzzard, Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the FLT LICENSE.

Adapted for this project from
https://github.com/ImperialCollegeLondon/FLT/blob/071d16bb51e87165b4f4b5466f14051344bf426b/FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean.
-/

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Linear maps of restricted products

Linear versions of mathlib's additive restricted-product transport maps. They are reusable
analytic infrastructure for finite-adelic and local-field constructions.
-/

open scoped RestrictedProduct

namespace RestrictedProduct

section Modules

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : Filter.Tendsto f 𝓕₂ 𝓕₁)
variable {A : Type*} [Semiring A]
variable [Π i, AddCommMonoid (R₁ i)] [Π i, AddCommMonoid (R₂ i)] [Π i, Module A (R₁ i)]
  [Π i, Module A (R₂ i)] [∀ i, AddSubmonoidClass (S₁ i) (R₁ i)]
  [∀ i, AddSubmonoidClass (S₂ i) (R₂ i)] [∀ i, SMulMemClass (S₁ i) A (R₁ i)]
  [∀ i, SMulMemClass (S₂ i) A (R₂ i)]
  (φ : ∀ j, R₁ (f j) →ₗ[A] R₂ j)
  (hφ : ∀ᶠ j in 𝓕₂, Set.MapsTo (φ j) (B₁ (f j)) (B₂ j))

/-- The linear map induced componentwise by eventually compatible linear maps. -/
def mapAlongLinearMap :
    Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →ₗ[A] Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  map_smul' a x := by
    ext i
    exact map_smul (φ i) a (x (f i))

@[simp]
theorem mapAlongLinearMap_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    mapAlongLinearMap R₁ R₂ f hf φ hφ x j = φ j (x (f j)) :=
  rfl

variable (A : Type*) [CommRing A] {ι : Type*} (R : ι → Type*)
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] (C : ∀ i, Submodule A (R i))

/-- Linear inclusion when one restricted-product condition refines another. -/
def inclusionLinearMap {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕] :=
  mapAlongLinearMap R R id h (fun _ ↦ LinearMap.id)
    (Filter.Eventually.of_forall fun _ _ ↦ id)

@[simp]
theorem inclusionLinearMap_apply {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖)
    (x : Πʳ i, [R i, C i]_[𝓖]) :
    inclusionLinearMap A R C h x = ⟨x.1, x.2.filter_mono h⟩ :=
  rfl

end Modules

end RestrictedProduct
