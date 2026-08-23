import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The local rings of an affine scheme

The stalk of `Spec R` at a prime `𝔭` is `R_𝔭`, and for a field the single stalk and the residue
field are the field itself.  The first is mathlib's `StructureSheaf.stalkIso`, transported to the
scheme's own structure sheaf; the second follows because a prime of a field is `(0)`, so every
element outside it is already invertible and the localization map is an isomorphism.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The stalk of `Spec R` at a prime is the localization of `R` there. -/
def specStalkRingEquiv (R : CommRingCat.{u}) (x : Spec R) :
    Localization.AtPrime x.asIdeal ≃+* ((Spec R).presheaf.stalk x) :=
  (StructureSheaf.stalkIso R x).toRingEquiv

/-- Transfer of `IsField` along a ring isomorphism. -/
theorem isField_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : IsField A) : IsField B := by
  haveI : Nontrivial A := ⟨h.exists_pair_ne⟩
  refine ⟨⟨e 0, e 1, fun hc => zero_ne_one (α := A) (e.injective hc)⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := h.mul_inv_cancel (a := e.symm a) (fun hc => ha (by
    rw [← e.apply_symm_apply a, hc, map_zero]))
  exact ⟨e b, by rw [← e.apply_symm_apply a, ← map_mul, hb, map_one]⟩

variable (K : Type u) [Field K]

/-- The stalk of `Spec` of a field at its unique point is the field. -/
def specFieldStalkEquiv (x : Spec (CommRingCat.of K)) :
    K ≃+* ((Spec (CommRingCat.of K)).presheaf.stalk x) :=
  (IsLocalization.atUnits (R := K) (S := Localization.AtPrime x.asIdeal)
    x.asIdeal.primeCompl (by
      intro a ha
      have hbot : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
      have hne : a ≠ 0 := by
        intro h
        apply ha
        rw [h, hbot]
        exact Ideal.zero_mem _
      exact ⟨Units.mk0 a hne, rfl⟩)).toRingEquiv.trans (specStalkRingEquiv _ x)

theorem specField_stalk_isField (x : Spec (CommRingCat.of K)) :
    IsField ((Spec (CommRingCat.of K)).presheaf.stalk x) :=
  isField_of_ringEquiv (specFieldStalkEquiv K x) (Field.toIsField K)

/-- For a local ring which is a field, the residue field is the ring itself. -/
def isFieldResidueFieldEquiv {R : Type*} [CommRing R] [IsLocalRing R] (h : IsField R) :
    IsLocalRing.ResidueField R ≃+* R :=
  (Ideal.quotEquivOfEq (IsLocalRing.isField_iff_maximalIdeal_eq.mp h)).trans
    (RingEquiv.quotientBot R)

/-- The residue field of `Spec` of a field at its unique point is the field. -/
def specFieldResidueFieldEquiv (x : Spec (CommRingCat.of K)) :
    K ≃+* ((Spec (CommRingCat.of K)).residueField x) :=
  (specFieldStalkEquiv K x).trans (isFieldResidueFieldEquiv (specField_stalk_isField K x)).symm

theorem specField_residueField_isField (x : Spec (CommRingCat.of K)) :
    IsField ((Spec (CommRingCat.of K)).residueField x) :=
  isField_of_ringEquiv (specFieldResidueFieldEquiv K x) (Field.toIsField K)

/-! ### The two stalks of a local domain -/

/-- The stalk of `Spec R` at the closed point of a local ring is the ring itself. -/
def specClosedStalkEquiv (R : CommRingCat.{u}) [IsLocalRing R] (x : Spec R)
    (hx : x.asIdeal = IsLocalRing.maximalIdeal R) :
    (R : Type u) ≃+* ((Spec R).presheaf.stalk x) :=
  (IsLocalization.atUnits (R := (R : Type u)) (S := Localization.AtPrime x.asIdeal)
    x.asIdeal.primeCompl (by
      intro a ha
      have hna : a ∉ x.asIdeal := ha
      rw [hx] at hna
      exact IsLocalRing.notMem_maximalIdeal.1 hna)).toRingEquiv.trans (specStalkRingEquiv R x)

theorem primeCompl_bot_eq_nonZeroDivisors (A : Type u) [CommRing A] [IsDomain A] :
    (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
  ext a
  simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]

/-- The stalk of `Spec R` at the generic point of a domain is the fraction field. -/
def specGenericStalkEquiv (R : CommRingCat.{u}) [IsDomain R] (x : Spec R)
    (hx : x.asIdeal = ⊥) :
    FractionRing (R : Type u) ≃+* ((Spec R).presheaf.stalk x) := by
  haveI : IsLocalization x.asIdeal.primeCompl (FractionRing (R : Type u)) := by
    have h1 : x.asIdeal.primeCompl = nonZeroDivisors (R : Type u) := by
      ext a
      show a ∉ x.asIdeal ↔ _
      rw [hx, mem_nonZeroDivisors_iff_ne_zero]
      simp
    rw [h1]
    infer_instance
  exact (IsLocalization.algEquiv x.asIdeal.primeCompl (FractionRing (R : Type u))
    (Localization.AtPrime x.asIdeal)).toRingEquiv.trans (specStalkRingEquiv R x)

end

end HTGeometry
