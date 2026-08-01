import GaloisForLFunctions.HTGeometry.FixedFieldDichotomy

/-!
# A symmetric Galois group has one quadratic subextension

A subgroup of index two is normal with quotient of order two, hence abelian, so in a symmetric group
it must be the alternating group.  By the Galois correspondence an extension whose group is
symmetric therefore has exactly one quadratic subextension.

So any square root of a base element lying in such an extension generates the alternating fixed
field, which is what identifies its square class with that of the discriminant.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **An index-two subgroup of a symmetric group is the alternating group.** -/
theorem eq_alternatingGroup_of_index_eq_two [Nontrivial α] {N : Subgroup (Equiv.Perm α)}
    (h : N.index = 2) : N = alternatingGroup α := by
  haveI : N.Normal := Subgroup.normal_of_index_eq_two h
  have hcard : Nat.card (Equiv.Perm α ⧸ N) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (Equiv.Perm α ⧸ N) := isCyclic_of_prime_card hcard
  have habel : ∀ x y : Equiv.Perm α ⧸ N, x * y = y * x := by
    intro x y
    letI := IsCyclic.commGroup (α := Equiv.Perm α ⧸ N)
    exact mul_comm x y
  rcases eq_alternatingGroup_or_top_of_abelian_quotient habel with h1 | h2
  · exact h1
  · exfalso
    rw [h2, Subgroup.index_top] at h
    exact absurd h (by norm_num)

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **An extension with symmetric Galois group has at most one quadratic subextension.** -/
theorem eq_of_finrank_eq_two_of_permGal [FiniteDimensional F E] [IsGalois F E] [Nontrivial α]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm α)
    {K₁ K₂ : IntermediateField F E} (h1 : Module.finrank F K₁ = 2)
    (h2 : Module.finrank F K₂ = 2) : K₁ = K₂ := by
  have hi : ∀ K : IntermediateField F E, Module.finrank F K = 2 →
      Subgroup.map (φ : (E ≃ₐ[F] E) →* Equiv.Perm α) K.fixingSubgroup = alternatingGroup α := by
    intro K hK
    refine eq_alternatingGroup_of_index_eq_two ?_
    have hidx := Subgroup.index_comap_of_surjective
      (H := Subgroup.map (φ : (E ≃ₐ[F] E) →* Equiv.Perm α) K.fixingSubgroup)
      (f := (φ : (E ≃ₐ[F] E) →* Equiv.Perm α)) φ.surjective
    rw [Subgroup.comap_map_eq_self_of_injective φ.injective] at hidx
    rw [← hidx, ← finrank_fixedField_eq_index, IsGalois.fixedField_fixingSubgroup, hK]
  have hself : ∀ K : IntermediateField F E,
      Subgroup.comap (φ : (E ≃ₐ[F] E) →* Equiv.Perm α)
        (Subgroup.map (φ : (E ≃ₐ[F] E) →* Equiv.Perm α) K.fixingSubgroup) = K.fixingSubgroup :=
    fun K => Subgroup.comap_map_eq_self_of_injective φ.injective _
  have hfix : K₁.fixingSubgroup = K₂.fixingSubgroup := by
    rw [← hself K₁, ← hself K₂, hi K₁ h1, hi K₂ h2]
  have he1 := IsGalois.fixedField_fixingSubgroup (F := F) (E := E) K₁
  have he2 := IsGalois.fixedField_fixingSubgroup (F := F) (E := E) K₂
  rw [← he1, ← he2, hfix]

end GaloisForLFunctions.HTGeometry
