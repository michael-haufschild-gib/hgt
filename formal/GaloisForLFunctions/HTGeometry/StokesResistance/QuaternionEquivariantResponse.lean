import GaloisForLFunctions.HTGeometry.StokesResistance.QuaternionArtinApplication
import GaloisForLFunctions.HTGeometry.GroupCharacter.FDRepBridge

/-!
# Quaternionic equivariant-response count

This module applies Moreau's equivariant-map character count to the corpus's literal
two-dimensional `Q₈` Artin carrier. The carrier itself has no invariant vector, but its
self-equivariant linear maps form exactly the scalar line. Therefore the normalized self-character
pairing is one.

In response language, quaternionic symmetry removes every preferred vector while retaining one
isotropic linear response coefficient. In Artin language, this is the exact Schur self-pairing of
the quaternionic representation.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

open MonoidAlgebra Representation
open RHTower

/-- Every endomorphism commuting with the literal `Q₈` action is scalar. -/
theorem deningerQ8_schur
    (f : Q8Carrier →ₗ[ℂ] Q8Carrier)
    (hf : ∀ g : QuaternionGroup 2,
      (deningerQ8Representation g) ∘ₗ f = f ∘ₗ (deningerQ8Representation g)) :
    ∃ c : ℂ, ∀ v, f v = c • v := by
  let e₁ : Q8Carrier := (1, 0)
  let e₂ : Q8Carrier := (0, 1)
  let c : ℂ := (f e₁).1
  have hI₁ := congrArg (fun L : Q8Carrier →ₗ[ℂ] Q8Carrier => L e₁)
    (hf (QuaternionGroup.a 1))
  have hI₂ := congrArg (fun L : Q8Carrier →ₗ[ℂ] Q8Carrier => L e₂)
    (hf (QuaternionGroup.a 1))
  have h₁snd : (f e₁).2 = 0 := by
    have h := congrArg Prod.snd hI₁
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    rw [deningerQ8Representation_a_one_apply,
      deningerQ8Representation_a_one_apply] at h
    dsimp [deningerQuaternionTransitionI, e₁] at h
    norm_num at h
    have hmap := congrArg Prod.snd (f.map_smul Complex.I (1, 0))
    have hmap' : (f (Complex.I, 0)).2 = Complex.I * (f (1, 0)).2 := by
      simpa using hmap
    rw [hmap'] at h
    have htwoI : (2 * Complex.I) * (f e₁).2 = 0 := by
      linear_combination -h
    exact (mul_eq_zero.mp htwoI).resolve_left
      (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have h₂fst : (f e₂).1 = 0 := by
    have h := congrArg Prod.fst hI₂
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    rw [deningerQ8Representation_a_one_apply,
      deningerQ8Representation_a_one_apply] at h
    dsimp [deningerQuaternionTransitionI, e₂] at h
    norm_num at h
    have hmap := congrArg Prod.fst (f.map_smul (-Complex.I) (0, 1))
    have hmap' : (f (0, -Complex.I)).1 = (-Complex.I) * (f (0, 1)).1 := by
      simpa using hmap
    rw [hmap'] at h
    have htwoI : (2 * Complex.I) * (f e₂).1 = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp htwoI).resolve_left
      (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hK := congrArg (fun L : Q8Carrier →ₗ[ℂ] Q8Carrier => L e₁)
    (hf (QuaternionGroup.xa 0))
  have he₂ : f e₂ = (0, c) := by
    simp only [LinearMap.coe_comp, Function.comp_apply] at hK
    rw [deningerQ8Representation_xa_zero_apply,
      deningerQ8Representation_xa_zero_apply] at hK
    have hKe₁ : deningerQuaternionTransitionK e₁ = e₂ := by
      simp [deningerQuaternionTransitionK, e₁, e₂]
    rw [hKe₁] at hK
    apply Prod.ext
    · exact h₂fst
    · change (f e₂).2 = c
      rw [← hK]
      exact rfl
  refine ⟨c, ?_⟩
  rintro ⟨x, y⟩
  have hv : (x, y) = x • e₁ + y • e₂ := by
    ext <;> simp [e₁, e₂]
  rw [hv, f.map_add, f.map_smul, f.map_smul]
  have he₁ : f e₁ = (c, 0) := by
    apply Prod.ext
    · rfl
    · exact h₁snd
  rw [he₁, he₂]
  ext <;> simp [e₁, e₂, mul_comm]

/-- Exact Moreau equivariant-response dimension for the `Q₈` carrier. -/
theorem deningerQ8_selfIntertwining_finrank :
    Module.finrank ℂ
      (Representation.IntertwiningMap deningerQ8Representation
        deningerQ8Representation) = 1 := by
  rw [← LinearEquiv.finrank_eq
    (Representation.invariantsEquivIntertwiningMap deningerQ8Representation
      deningerQ8Representation)]
  exact GaloisForLFunctions.HTGeometry.GroupCharacter.finrank_invariants_linHom_eq_one
    deningerQ8Representation deningerQ8_schur

/-- The normalized quaternionic Artin self-character pairing is one. -/
theorem deningerQ8_character_self_average_eq_one :
    (Fintype.card (QuaternionGroup 2) : ℂ)⁻¹ *
      ∑ g : QuaternionGroup 2,
        LinearMap.trace ℂ Q8Carrier (deningerQ8Representation g⁻¹) *
          LinearMap.trace ℂ Q8Carrier (deningerQ8Representation g) = 1 := by
  change (Fintype.card (QuaternionGroup 2) : ℂ)⁻¹ *
      ∑ g : QuaternionGroup 2,
        Representation.character
            (deningerQ8Representation :
              Representation ℂ (QuaternionGroup 2) Q8Carrier) g⁻¹ *
          Representation.character
            (deningerQ8Representation :
              Representation ℂ (QuaternionGroup 2) Q8Carrier) g = 1
  rw [← finrank_intertwiningMap_eq_character_product_average,
    deningerQ8_selfIntertwining_finrank]
  norm_num

end GaloisForLFunctions.HTGeometry.StokesResistance
