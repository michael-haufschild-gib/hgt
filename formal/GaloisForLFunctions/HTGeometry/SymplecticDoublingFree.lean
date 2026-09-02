import Mathlib

/-!
# Doubling is free for symplectic self-adjointness; quadratic symbols are symmetric

* Given any nondegenerate symmetric `K`-self-adjoint bilinear form `S` on `V`, the doubled form
  `ω((x₁,x₂),(y₁,y₂)) = S x₁ y₂ − S x₂ y₁` on `V × V` is nondegenerate, alternating, and
  `K ⊕ K`-self-adjoint.  Doubling any block therefore produces a symplectic self-adjoint
  realization for free, so realizations of doubled models carry no information about the
  original block.  (The complementary fact, that a single cyclic block carries no such form, is
  `RHTower.SymplecticCyclicObstruction`.)

* A pairing with values in `{±1}` that is skew, `b x y · b y x = 1`, is symmetric.  Quadratic
  symbols therefore define symmetric, not alternating, forms.
-/

namespace GaloisForLFunctions.HTGeometry

section Doubling

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The doubled form `ω((x₁,x₂),(y₁,y₂)) = S x₁ y₂ − S x₂ y₁` on `V × V`. -/
def doubledForm (S : LinearMap.BilinForm k V) : LinearMap.BilinForm k (V × V) :=
  LinearMap.mk₂ k (fun p q => S p.1 q.2 - S p.2 q.1)
    (by
      intro p p' q
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      ring)
    (by
      intro c p q
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (by
      intro p q q'
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      ring)
    (by
      intro c p q
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
      ring)

theorem doubledForm_apply (S : LinearMap.BilinForm k V) (p q : V × V) :
    doubledForm S p q = S p.1 q.2 - S p.2 q.1 := by
  rw [doubledForm, LinearMap.mk₂_apply]

/-- The doubled form of a symmetric form is alternating. -/
theorem doubledForm_isAlt (S : LinearMap.BilinForm k V) (hS : ∀ x y, S x y = S y x) :
    (doubledForm S).IsAlt := by
  intro p
  rw [doubledForm_apply, hS p.1 p.2, sub_self]

/-- The doubled form of a nondegenerate form is nondegenerate. -/
theorem doubledForm_nondegenerate (S : LinearMap.BilinForm k V) (hnd : S.Nondegenerate) :
    (doubledForm S).Nondegenerate := by
  refine ⟨fun p hp => ?_, fun q hq => ?_⟩
  · have h1 : p.1 = 0 := by
      refine hnd.1 p.1 fun w => ?_
      have := hp (0, w)
      simpa [doubledForm_apply] using this
    have h2 : p.2 = 0 := by
      refine hnd.1 p.2 fun w => ?_
      have := hp (w, 0)
      simpa [doubledForm_apply] using this
    exact Prod.ext h1 h2
  · have h1 : q.1 = 0 := by
      refine hnd.2 q.1 fun w => ?_
      have := hq (0, w)
      simpa [doubledForm_apply] using this
    have h2 : q.2 = 0 := by
      refine hnd.2 q.2 fun w => ?_
      have := hq (w, 0)
      simpa [doubledForm_apply] using this
    exact Prod.ext h1 h2

/-- The diagonal endomorphism `K ⊕ K` is self-adjoint for the doubled form whenever `K` is
self-adjoint for `S`. -/
theorem doubledForm_selfAdjoint (S : LinearMap.BilinForm k V) (K : Module.End k V)
    (hK : ∀ x y, S (K x) y = S x (K y)) (p q : V × V) :
    doubledForm S (K.prodMap K p) q = doubledForm S p (K.prodMap K q) := by
  simp only [doubledForm_apply, LinearMap.prodMap_apply, hK]

/-- **Doubling is free.**  Any nondegenerate symmetric `K`-self-adjoint form on `V` yields a
nondegenerate alternating form on `V × V` for which `K ⊕ K` is self-adjoint. -/
theorem exists_symplectic_selfAdjoint_doubled (S : LinearMap.BilinForm k V)
    (hnd : S.Nondegenerate) (hS : ∀ x y, S x y = S y x) (K : Module.End k V)
    (hK : ∀ x y, S (K x) y = S x (K y)) :
    ∃ ω : LinearMap.BilinForm k (V × V), ω.Nondegenerate ∧ ω.IsAlt ∧
      ∀ p q, ω (K.prodMap K p) q = ω p (K.prodMap K q) :=
  ⟨doubledForm S, doubledForm_nondegenerate S hnd, doubledForm_isAlt S hS,
    doubledForm_selfAdjoint S K hK⟩

end Doubling

section Sign

/-- A skew pairing with values in `{±1}` is symmetric. -/
theorem symm_of_skew_units {α : Type*} (b : α → α → ℤˣ) (h : ∀ x y, b x y * b y x = 1)
    (x y : α) : b x y = b y x := by
  have h1 : b y x = (b x y)⁻¹ := (inv_eq_of_mul_eq_one_right (h x y)).symm
  have h2 : (b x y)⁻¹ = b x y := by
    rcases Int.units_eq_one_or (b x y) with h | h <;> simp [h]
  rw [h1, h2]

end Sign

end GaloisForLFunctions.HTGeometry
