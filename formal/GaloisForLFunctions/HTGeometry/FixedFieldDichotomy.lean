import GaloisForLFunctions.HTGeometry.SymmetricGroupCommutator
import Mathlib.FieldTheory.Galois.Basic

/-!
# An intermediate field with abelian Galois quotient is the base or the alternating fixed field

For a finite Galois extension whose group is isomorphic to a symmetric group, an intermediate field
whose fixing subgroup is normal with abelian quotient has that fixing subgroup equal to the whole
group or to the preimage of the alternating group.

By the Galois correspondence the field itself is therefore the base or the fixed field of that
preimage.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **The intermediate field dichotomy.** -/
theorem eq_bot_or_eq_fixedField_alternating [FiniteDimensional F E] [IsGalois F E]
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm α)
    (K : IntermediateField F E) [K.fixingSubgroup.Normal]
    (habel : ∀ x y : (E ≃ₐ[F] E) ⧸ K.fixingSubgroup, x * y = y * x) :
    K = ⊥ ∨
      K = IntermediateField.fixedField
        (Subgroup.comap (φ : (E ≃ₐ[F] E) →* Equiv.Perm α) (alternatingGroup α)) := by
  have hself : Subgroup.comap (φ : (E ≃ₐ[F] E) →* Equiv.Perm α)
      (Subgroup.map (φ : (E ≃ₐ[F] E) →* Equiv.Perm α) K.fixingSubgroup) = K.fixingSubgroup :=
    Subgroup.comap_map_eq_self_of_injective φ.injective _
  rcases map_eq_alternatingGroup_or_top φ K.fixingSubgroup habel with h | h
  · right
    rw [← h, hself, IsGalois.fixedField_fixingSubgroup]
  · left
    have htop : K.fixingSubgroup = ⊤ := by
      rw [← hself, h, Subgroup.comap_top]
    have hfix : IntermediateField.fixedField K.fixingSubgroup = K :=
      IsGalois.fixedField_fixingSubgroup K
    rw [← hfix, htop, IsGalois.fixedField_top]

/-! ## The degree of a fixed field is the index -/

/-- **The degree of a fixed field over the base is the index of the subgroup.** -/
theorem finrank_fixedField_eq_index [FiniteDimensional F E] [IsGalois F E]
    (H : Subgroup (E ≃ₐ[F] E)) :
    Module.finrank F (IntermediateField.fixedField H) = H.index := by
  classical
  have hcard : Module.finrank (IntermediateField.fixedField H) E = Nat.card H :=
    IntermediateField.finrank_fixedField_eq_card H
  have htower : Module.finrank F (IntermediateField.fixedField H) *
      Module.finrank (IntermediateField.fixedField H) E = Module.finrank F E :=
    Module.finrank_mul_finrank F (IntermediateField.fixedField H) E
  have hgal : Nat.card (E ≃ₐ[F] E) = Module.finrank F E := IsGalois.card_aut_eq_finrank F E
  have hindex : Nat.card H * H.index = Nat.card (E ≃ₐ[F] E) := Subgroup.card_mul_index H
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [hcard] at htower
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [htower, ← hgal, ← hindex]
  ring

/-- **The alternating fixed field is quadratic over the base.** -/
theorem finrank_fixedField_alternating [FiniteDimensional F E] [IsGalois F E]
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm α) :
    Module.finrank F (IntermediateField.fixedField
      (Subgroup.comap (φ : (E ≃ₐ[F] E) →* Equiv.Perm α) (alternatingGroup α))) = 2 := by
  rw [finrank_fixedField_eq_index, Subgroup.index_comap_of_surjective _ φ.surjective]
  exact alternatingGroup.index_eq_two

/-- **The degree dichotomy.**  An intermediate field whose fixing subgroup is normal with abelian
quotient has degree one or two over the base. -/
theorem finrank_eq_one_or_two_of_abelian_quotient [FiniteDimensional F E] [IsGalois F E]
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm α)
    (K : IntermediateField F E) [K.fixingSubgroup.Normal]
    (habel : ∀ x y : (E ≃ₐ[F] E) ⧸ K.fixingSubgroup, x * y = y * x) :
    Module.finrank F K = 1 ∨ Module.finrank F K = 2 := by
  rcases eq_bot_or_eq_fixedField_alternating φ K habel with h | h
  · left
    rw [h, IntermediateField.finrank_bot]
  · right
    rw [h, finrank_fixedField_alternating]

end GaloisForLFunctions.HTGeometry
