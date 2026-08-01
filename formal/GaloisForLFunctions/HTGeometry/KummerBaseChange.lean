import GaloisForLFunctions.HTGeometry.KummerInfBot
import GaloisForLFunctions.HTGeometry.SquareRootObstruction
import GaloisForLFunctions.HTGeometry.NaturalIrrationalities
import GaloisForLFunctions.HTGeometry.FixedFieldDichotomy
import GaloisForLFunctions.HTGeometry.IntermediateFieldComap

/-!
# Base change along a Kummer extension preserves the Galois group

When the intersection of a Galois extension with a second factor of a compositum is the base,
restriction is an isomorphism of automorphism groups.  The intersection is the base as soon as it
is at most quadratic and no square root of a base element lies in the second factor.

For a second factor of odd degree that square root condition is automatic, so base change along an
odd-degree extension never shrinks the group.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **Base change preserves the Galois group when no square root survives.** -/
noncomputable def kummerBaseChangeEquiv [CharZero F] {E M : IntermediateField F L} [Normal F E]
    [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional M L] [IsGalois M L]
    (hEM : E ⊔ M = ⊤)
    (hdeg : Module.finrank F (E ⊓ M : IntermediateField F L) = 1 ∨
      Module.finrank F (E ⊓ M : IntermediateField F L) = 2)
    (hobs : ∀ (δ : L) (c : F), δ * δ = algebraMap F L c →
      δ ∉ (⊥ : IntermediateField F L) → δ ∉ M) :
    (L ≃ₐ[M] L) ≃* (E ≃ₐ[F] E) :=
  compositumRestrictEquiv hEM (inf_eq_bot_of_no_sqrt hdeg hobs)

/-- Over an odd-degree second factor no square root of a base element survives. -/
theorem no_sqrt_of_not_two_dvd_finrank {M : IntermediateField F L} [FiniteDimensional F M]
    (hodd : ¬ 2 ∣ Module.finrank F M) :
    ∀ (δ : L) (c : F), δ * δ = algebraMap F L c →
      δ ∉ (⊥ : IntermediateField F L) → δ ∉ M :=
  fun _ _ hsq hbot => notMem_of_not_two_dvd_finrank hodd hsq hbot

/-- **Base change along an odd-degree extension preserves the Galois group.** -/
noncomputable def oddBaseChangeEquiv [CharZero F] {E M : IntermediateField F L} [Normal F E]
    [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional M L] [IsGalois M L]
    [FiniteDimensional F M]
    (hEM : E ⊔ M = ⊤)
    (hdeg : Module.finrank F (E ⊓ M : IntermediateField F L) = 1 ∨
      Module.finrank F (E ⊓ M : IntermediateField F L) = 2)
    (hodd : ¬ 2 ∣ Module.finrank F M) :
    (L ≃ₐ[M] L) ≃* (E ≃ₐ[F] E) :=
  kummerBaseChangeEquiv hEM hdeg (no_sqrt_of_not_two_dvd_finrank hodd)

/-- **The full symmetric monodromy survives the base change.**  This is the shape of the
rank-one statement: the group over the larger field is still the symmetric group. -/
noncomputable def kummerBaseChangePermEquiv [CharZero F] {E M : IntermediateField F L}
    [Normal F E] [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional M L] [IsGalois M L]
    {m : ℕ}
    (hEM : E ⊔ M = ⊤)
    (hdeg : Module.finrank F (E ⊓ M : IntermediateField F L) = 1 ∨
      Module.finrank F (E ⊓ M : IntermediateField F L) = 2)
    (hobs : ∀ (δ : L) (c : F), δ * δ = algebraMap F L c →
      δ ∉ (⊥ : IntermediateField F L) → δ ∉ M)
    (hiso : (E ≃ₐ[F] E) ≃* Equiv.Perm (Fin m)) :
    (L ≃ₐ[M] L) ≃* Equiv.Perm (Fin m) :=
  (kummerBaseChangeEquiv hEM hdeg hobs).trans hiso

/-- **Base change preserves the Galois group, root form.**  The dichotomy is supplied as an explicit
square root rather than as a degree. -/
noncomputable def kummerBaseChangeEquivOfRoot {E M : IntermediateField F L} [Normal F E]
    [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional M L] [IsGalois M L]
    (hEM : E ⊔ M = ⊤)
    (hdich : (E ⊓ M : IntermediateField F L) = ⊥ ∨
      ∃ (δ : L) (c : F), δ ∈ (E ⊓ M : IntermediateField F L) ∧
        δ * δ = algebraMap F L c ∧ δ ∉ (⊥ : IntermediateField F L))
    (hobs : ∀ (δ : L) (c : F), δ * δ = algebraMap F L c →
      δ ∉ (⊥ : IntermediateField F L) → δ ∉ M) :
    (L ≃ₐ[M] L) ≃* (E ≃ₐ[F] E) :=
  compositumRestrictEquiv hEM (inf_eq_bot_of_no_sqrt_of_root hdich hobs)

/-- **The full symmetric monodromy survives, root form.** -/
noncomputable def kummerBaseChangePermEquivOfRoot {E M : IntermediateField F L} [Normal F E]
    [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional M L] [IsGalois M L] {m : ℕ}
    (hEM : E ⊔ M = ⊤)
    (hdich : (E ⊓ M : IntermediateField F L) = ⊥ ∨
      ∃ (δ : L) (c : F), δ ∈ (E ⊓ M : IntermediateField F L) ∧
        δ * δ = algebraMap F L c ∧ δ ∉ (⊥ : IntermediateField F L))
    (hobs : ∀ (δ : L) (c : F), δ * δ = algebraMap F L c →
      δ ∉ (⊥ : IntermediateField F L) → δ ∉ M)
    (hiso : (E ≃ₐ[F] E) ≃* Equiv.Perm (Fin m)) :
    (L ≃ₐ[M] L) ≃* Equiv.Perm (Fin m) :=
  (kummerBaseChangeEquivOfRoot hEM hdich hobs).trans hiso

/-! ## The fully assembled statement -/

/-- **Base change along a second factor preserves the Galois group.**  The intersection is
controlled by the group side -- its fixing subgroup is normal with abelian quotient -- and excluded
by the field side, since no square root of a base element lies in the second factor. -/
noncomputable def kummerBaseChangeOfAbelian [CharZero F] {E M : IntermediateField F L}
    [Normal F E] [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional M L] [IsGalois M L]
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm α)
    (hEM : E ⊔ M = ⊤)
    (hnorm : (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup.Normal)
    (habel : ∀ x y : (E ≃ₐ[F] E) ⧸
      (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup, x * y = y * x)
    (hobs : ∀ (δ : L) (c : F), δ * δ = algebraMap F L c →
      δ ∉ (⊥ : IntermediateField F L) → δ ∉ M) :
    (L ≃ₐ[M] L) ≃* (E ≃ₐ[F] E) := by
  haveI := hnorm
  have hdeg' := finrank_eq_one_or_two_of_abelian_quotient φ
    (IntermediateField.comap E.val (E ⊓ M)) habel
  rw [finrank_comap_val (inf_le_left : (E ⊓ M : IntermediateField F L) ≤ E)] at hdeg'
  exact kummerBaseChangeEquiv hEM hdeg' hobs

/-- **The full symmetric monodromy survives, assembled form.** -/
noncomputable def kummerBaseChangePermOfAbelian [CharZero F] {E M : IntermediateField F L}
    [Normal F E] [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional M L] [IsGalois M L]
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm α)
    (hEM : E ⊔ M = ⊤)
    (hnorm : (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup.Normal)
    (habel : ∀ x y : (E ≃ₐ[F] E) ⧸
      (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup, x * y = y * x)
    (hobs : ∀ (δ : L) (c : F), δ * δ = algebraMap F L c →
      δ ∉ (⊥ : IntermediateField F L) → δ ∉ M) :
    (L ≃ₐ[M] L) ≃* Equiv.Perm α :=
  (kummerBaseChangeOfAbelian φ hEM hnorm habel hobs).trans φ

end GaloisForLFunctions.HTGeometry
