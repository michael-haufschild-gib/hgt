import Mathlib.FieldTheory.Galois.Basic

/-!
# Transferring commutativity along surjections and the Galois correspondence

A surjective image of an abelian group is abelian, and for a finite Galois extension the quotient of
the automorphism group by a normal subgroup is the automorphism group of the fixed field.

So an intermediate field whose own automorphism group is abelian -- for instance a subextension of a
Kummer extension -- gives an abelian quotient, which is the group-side hypothesis of the base change
step.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A surjective image of an abelian group is abelian.** -/
theorem commute_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (hG : ∀ x y : G, x * y = y * x) :
    ∀ x y : H, x * y = y * x := by
  intro x y
  obtain ⟨x', rfl⟩ := hf x
  obtain ⟨y', rfl⟩ := hf y
  rw [← map_mul, ← map_mul, hG]

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **The quotient by a normal subgroup is abelian when the fixed field has abelian automorphism
group.** -/
theorem commute_quotient_of_commute_gal [FiniteDimensional F E] [IsGalois F E]
    {H : Subgroup (E ≃ₐ[F] E)} [H.Normal]
    (h : ∀ x y : ((IntermediateField.fixedField H) ≃ₐ[F] (IntermediateField.fixedField H)),
      x * y = y * x) :
    ∀ x y : (E ≃ₐ[F] E) ⧸ H, x * y = y * x := by
  intro x y
  obtain ⟨x', rfl⟩ := (IsGalois.normalAutEquivQuotient H).symm.surjective x
  obtain ⟨y', rfl⟩ := (IsGalois.normalAutEquivQuotient H).symm.surjective y
  rw [← map_mul, ← map_mul, h]

/-- **Commutativity descends to a normal subextension.** -/
theorem commute_gal_of_le {K M : Type*} [Field K] [Field M] [Algebra F K] [Algebra F M]
    [Algebra K M] [IsScalarTower F K M] [Normal F K] [Normal F M]
    (hM : ∀ x y : (M ≃ₐ[F] M), x * y = y * x) :
    ∀ x y : (K ≃ₐ[F] K), x * y = y * x :=
  commute_of_surjective (AlgEquiv.restrictNormalHom K)
    (AlgEquiv.restrictNormalHom_surjective M) hM

/-- **The composed transfer.**  If the fixed field of a normal subgroup sits inside an extension
with abelian automorphism group, the quotient by that subgroup is abelian.  This is the
group-side hypothesis of the base change step, discharged from a Kummer extension. -/
theorem commute_quotient_of_le_abelian [FiniteDimensional F E] [IsGalois F E]
    {H : Subgroup (E ≃ₐ[F] E)} [H.Normal] {M : Type*} [Field M] [Algebra F M]
    [Algebra (IntermediateField.fixedField H) M]
    [IsScalarTower F (IntermediateField.fixedField H) M]
    [Normal F (IntermediateField.fixedField H)] [Normal F M]
    (habelM : ∀ x y : (M ≃ₐ[F] M), x * y = y * x) :
    ∀ x y : (E ≃ₐ[F] E) ⧸ H, x * y = y * x :=
  commute_quotient_of_commute_gal (commute_gal_of_le habelM)

end GaloisForLFunctions.HTGeometry
