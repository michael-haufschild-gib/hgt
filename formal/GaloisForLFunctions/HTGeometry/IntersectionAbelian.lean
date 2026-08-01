import GaloisForLFunctions.HTGeometry.IntersectionFixingSubgroup
import GaloisForLFunctions.HTGeometry.AbelianQuotientTransfer

/-!
# The intersection inherits commutativity from the second factor

Restricting automorphisms of a normal subextension to a normal subextension of it is surjective, so
if the larger one has commutative automorphism group so does the smaller.  Applied to the
intersection of two normal subextensions, commutativity comes from the second factor alone.

Reading the intersection inside the first factor and passing to the quotient by the subgroup fixing
it turns this into the abelian-quotient hypothesis of the base change step.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **The intersection has commutative automorphism group.** -/
theorem commute_gal_inf (E M : IntermediateField F L) [Normal F L] [Normal F E] [Normal F M]
    (habelM : ∀ x y : (M ≃ₐ[F] M), x * y = y * x) :
    ∀ x y : ((E ⊓ M : IntermediateField F L) ≃ₐ[F] (E ⊓ M : IntermediateField F L)),
      x * y = y * x := by
  haveI : Normal F (IntermediateField.extendScalars (inf_le_right : E ⊓ M ≤ M)) :=
    inferInstanceAs (Normal F M)
  exact commute_gal_of_le (F := F) (K := (E ⊓ M : IntermediateField F L))
    (M := (IntermediateField.extendScalars (inf_le_right : E ⊓ M ≤ M))) habelM

/-- **The abelian-quotient hypothesis of the base change step.** -/
theorem commute_quotient_comap_inf (E M : IntermediateField F L)
    [Normal F L] [FiniteDimensional F E] [IsGalois F E] [Normal F M]
    (hnorm : (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup.Normal)
    (habelM : ∀ x y : (M ≃ₐ[F] M), x * y = y * x) :
    ∀ x y : (E ≃ₐ[F] E) ⧸ (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup,
      x * y = y * x := by
  haveI := hnorm
  haveI : Normal F E := IsGalois.to_normal
  refine commute_quotient_of_commute_gal ?_
  have hfix : IntermediateField.fixedField
      (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup =
      IntermediateField.comap E.val (E ⊓ M) :=
    IsGalois.fixedField_fixingSubgroup _
  rw [hfix]
  intro x y
  refine (AlgEquiv.autCongr (comapValEquiv (inf_le_left : E ⊓ M ≤ E))).injective ?_
  rw [map_mul, map_mul]
  exact commute_gal_inf E M habelM _ _

end GaloisForLFunctions.HTGeometry
