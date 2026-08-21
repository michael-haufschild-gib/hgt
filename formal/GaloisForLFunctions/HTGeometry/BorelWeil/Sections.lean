/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.BorelSubgroup
import Mathlib.RepresentationTheory.Basic

/-!
# Sections of the Borel–Weil line bundle

Let `G = SL(n,k)`, let `B` be the standard Borel subgroup of upper-triangular matrices, and let
`λ : n → ℕ` be a weight.  The line bundle `L_λ = G ×^B k_λ` on the flag variety `G/B` is the
associated bundle of the character `borelChar λ` of `B`; in this associated-bundle description its
space of global regular sections is

`H⁰(λ) = { f : G → k regular | f (g * b) = borelChar λ b * f g for all g ∈ G, b ∈ B }`,

which is what `bwSections λ` denotes here.  The group `G` acts on it by left translation,
`(x • f) g = f (x⁻¹ * g)`; this is the representation whose structure the Borel–Weil theorem
determines.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.bwSections` — the `k`-submodule of sections.
* `GaloisForLFunctions.HTGeometry.BorelWeil.bwRep` — the left-translation representation of
  `SL(n,k)` on the sections.
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {k : Type*} [CommRing k]

/-- The space of global sections of the Borel–Weil line bundle attached to the weight `lam`:
regular functions on `SL(n,k)` that transform by the character `borelChar lam` under right
translation by the standard Borel subgroup. -/
def bwSections (lam : n → ℕ) : Submodule k (SpecialLinearGroup n k → k) where
  carrier := {f | f ∈ regularFun n k ∧
    ∀ g b, b ∈ borel n k → f (g * b) = borelChar lam b * f g}
  add_mem' := by
    rintro f₁ f₂ ⟨hf₁, he₁⟩ ⟨hf₂, he₂⟩
    exact ⟨Subalgebra.add_mem _ hf₁ hf₂, fun g b hb => by
      simp only [Pi.add_apply, he₁ g b hb, he₂ g b hb, mul_add]⟩
  zero_mem' := ⟨Subalgebra.zero_mem _, by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, he⟩
    exact ⟨Subalgebra.smul_mem _ hf c, fun g b hb => by
      simp only [Pi.smul_apply, he g b hb, smul_eq_mul]; ring⟩

theorem mem_bwSections {lam : n → ℕ} {f : SpecialLinearGroup n k → k} :
    f ∈ bwSections lam ↔ f ∈ regularFun n k ∧
      ∀ g b, b ∈ borel n k → f (g * b) = borelChar lam b * f g := Iff.rfl

theorem bwSections_regular {lam : n → ℕ} {f : SpecialLinearGroup n k → k}
    (hf : f ∈ bwSections lam) : f ∈ regularFun n k := hf.1

theorem bwSections_equivariant {lam : n → ℕ} {f : SpecialLinearGroup n k → k}
    (hf : f ∈ bwSections lam) (g b : SpecialLinearGroup n k) (hb : b ∈ borel n k) :
    f (g * b) = borelChar lam b * f g := hf.2 g b hb

/-- Sections are stable under left translation. -/
theorem bwSections_leftTransl {lam : n → ℕ} (x : SpecialLinearGroup n k)
    {f : SpecialLinearGroup n k → k} (hf : f ∈ bwSections lam) :
    leftTransl x f ∈ bwSections lam := by
  refine ⟨regularFun_leftTransl x hf.1, fun g b hb => ?_⟩
  simp only [leftTransl_apply, ← mul_assoc]
  exact hf.2 (x * g) b hb

/-- The left-translation action of `SL(n,k)` on the space of sections, as a linear map. -/
noncomputable def bwActionMap (lam : n → ℕ) (x : SpecialLinearGroup n k) :
    bwSections (k := k) lam →ₗ[k] bwSections (k := k) lam where
  toFun f := ⟨leftTransl x⁻¹ (f : SpecialLinearGroup n k → k), bwSections_leftTransl _ f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem bwActionMap_coe (lam : n → ℕ) (x : SpecialLinearGroup n k)
    (f : bwSections (k := k) lam) (g : SpecialLinearGroup n k) :
    ((bwActionMap lam x f : SpecialLinearGroup n k → k)) g = (f : SpecialLinearGroup n k → k) (x⁻¹ * g) :=
  rfl

/-- The Borel–Weil representation: `SL(n,k)` acting on the sections of `L_λ` by left translation. -/
noncomputable def bwRep (lam : n → ℕ) :
    Representation k (SpecialLinearGroup n k) (bwSections (k := k) lam) where
  toFun := bwActionMap lam
  map_one' := by
    ext f g
    simp
  map_mul' x y := by
    ext f g
    simp [mul_assoc]

@[simp] theorem bwRep_apply (lam : n → ℕ) (x : SpecialLinearGroup n k)
    (f : bwSections (k := k) lam) (g : SpecialLinearGroup n k) :
    ((bwRep lam x f : SpecialLinearGroup n k → k)) g = (f : SpecialLinearGroup n k → k) (x⁻¹ * g) :=
  rfl

end GaloisForLFunctions.HTGeometry.BorelWeil
