import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicCompletionNormalization
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionUnitsReduction

/-! The p-adic identification of a completion carries integral units
and their reductions to p-adic units and reduction modulo p. -/

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Reciprocity

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime]

theorem exists_padic_residue_equiv_of_completion (v : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[p] ≃+* v.adicCompletion E) (hi : Continuous i) :
    ∃ e : (𝓞 E ⧸ v.asIdeal) ≃+* ZMod p, ∀ (u : unitsLevel (K := E) v 0),
      ∃ z : ℤ_[p]ˣ, (u.val : v.adicCompletion E) = i ((z : ℤ_[p]) : ℚ_[p]) ∧
        Units.map e.toRingHom.toMonoidHom (finiteCompletionUnitReduction v u) =
          Units.map PadicInt.toZMod.toMonoidHom z := by
  obtain ⟨w, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := E)).surjective v
  let v := w.maximalIdeal
  let r : ℤ_[p] ≃+* CompletedIntegers v := padicCompletionIntegersEquiv w i hi
  letI : IsLocalHom r.symm.toRingHom := IsLocalHom.of_surjective _ r.symm.surjective
  let e := (completedResidueEquiv v).trans ((IsLocalRing.ResidueField.mapEquiv r.symm).trans
    PadicInt.residueField)
  refine ⟨e, fun u => ?_⟩
  let x := unitsLevelZeroEquivIntegerUnits v u
  let z := Units.map r.symm.toRingHom.toMonoidHom x
  refine ⟨z, ?_, ?_⟩
  · have he : r (z : ℤ_[p]) = (x : CompletedIntegers v) := r.apply_symm_apply _
    exact (congrArg (fun y : CompletedIntegers v => y.val) he).symm
  · apply Units.ext
    change PadicInt.residueField
      ((IsLocalRing.ResidueField.mapEquiv r.symm) (completedResidueEquiv v (completionReduction v x.val))) =
      PadicInt.toZMod (z : ℤ_[p])
    rw [completedResidueEquiv_apply_completionReduction]
    change PadicInt.residueField (IsLocalRing.ResidueField.map r.symm.toRingHom
      (IsLocalRing.residue _ x.val)) = _
    rw [IsLocalRing.ResidueField.map_residue]
    change PadicInt.residueField (IsLocalRing.residue ℤ_[p] (r.symm (x : CompletedIntegers v))) =
      PadicInt.toZMod (r.symm (x : CompletedIntegers v))
    exact (DFunLike.congr_fun (PadicInt.toZMod_eq_residueField_comp_residue (p := p)) _).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_padic_residue_equiv_of_completion
