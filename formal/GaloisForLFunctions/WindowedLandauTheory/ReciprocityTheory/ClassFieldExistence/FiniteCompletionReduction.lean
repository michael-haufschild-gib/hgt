import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDegreeLowerBound

/-! Reduction of the completed integer ring has the original prime residue
field. Integral lifts from the number field compute this reduction. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

namespace GlobalTheory.Reciprocity

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

/-- The integral elements of the finite completion. -/
abbrev CompletedIntegers := (Valued.v : Valuation (u.adicCompletion F) ℤᵐ⁰).integer

/-- The embedding of global integers into completed integers. -/
def toCompletedIntegers : 𝓞 F →+* CompletedIntegers u :=
  (algebraMap (𝓞 F) (u.adicCompletion F)).codRestrict _
    (fun r => valued_algebraMap_int_le_one u r)

private theorem residue_eq_iff_valued_sub_lt_one (x y : CompletedIntegers u) :
    IsLocalRing.residue _ x = IsLocalRing.residue _ y ↔
      Valued.v ((x : u.adicCompletion F) - y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit (x - y) ↔ _
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

private def fromGlobalIntegerResidue : 𝓞 F →+* IsLocalRing.ResidueField (CompletedIntegers u) :=
  (IsLocalRing.residue _).comp (toCompletedIntegers u)

private theorem fromGlobalIntegerResidue_surjective :
    Function.Surjective (fromGlobalIntegerResidue u) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨r, hr⟩ := exists_int_valued_sub_lt_one u x.val x.2
  exact ⟨r, ((residue_eq_iff_valued_sub_lt_one u x (toCompletedIntegers u r)).mpr hr).symm⟩

private theorem ker_fromGlobalIntegerResidue :
    RingHom.ker (fromGlobalIntegerResidue u) = u.asIdeal := by
  ext r
  rw [RingHom.mem_ker]
  change IsLocalRing.residue _ (toCompletedIntegers u r) = 0 ↔ _
  rw [← map_zero (IsLocalRing.residue (CompletedIntegers u)),
    residue_eq_iff_valued_sub_lt_one]
  change Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) r - 0) < 1 ↔ _
  rw [sub_zero, valued_algebraMap_int_lt_one_iff]

/-- The prime residue field is the residue field of the completed integers. -/
def completedResidueEquiv : (𝓞 F ⧸ u.asIdeal) ≃+*
    IsLocalRing.ResidueField (CompletedIntegers u) :=
  (Ideal.quotEquivOfEq (ker_fromGlobalIntegerResidue u).symm).trans
    ((fromGlobalIntegerResidue u).quotientKerEquivOfSurjective
      (fromGlobalIntegerResidue_surjective u))

/-- Reduction to the residue field of the original prime. -/
def completionReduction : CompletedIntegers u →+* (𝓞 F ⧸ u.asIdeal) :=
  (completedResidueEquiv u).symm.toRingHom.comp (IsLocalRing.residue _)

theorem completionReduction_eq_iff (x y : CompletedIntegers u) :
    completionReduction u x = completionReduction u y ↔
      Valued.v ((x : u.adicCompletion F) - y) < 1 :=
  (completedResidueEquiv u).symm.injective.eq_iff.trans
    (residue_eq_iff_valued_sub_lt_one u x y)

@[simp] theorem completedResidueEquiv_apply_completionReduction (x : CompletedIntegers u) :
    completedResidueEquiv u (completionReduction u x) = IsLocalRing.residue _ x :=
  (completedResidueEquiv u).apply_symm_apply _

@[simp] theorem completionReduction_toCompletedIntegers (r : 𝓞 F) :
    completionReduction u (toCompletedIntegers u r) = Ideal.Quotient.mk _ r := by
  apply (completedResidueEquiv u).injective
  rw [show completedResidueEquiv u (completionReduction u (toCompletedIntegers u r)) =
      fromGlobalIntegerResidue u r from (completedResidueEquiv u).apply_symm_apply _]
  simp [completedResidueEquiv]

end GlobalTheory.Reciprocity
