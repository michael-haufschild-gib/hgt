import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStageInertia
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.TameArtinCharacters
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionUnitsReduction

/-! Inverse Artin on the lifted inertia gives a canonical quotient
over each tame stage. Approximation by global integers identifies
this quotient with any residue description for that stage. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}
  {p n : ℕ} [Fact p.Prime] (D : LocalTameStage h p n)

def LocalTameStage.residueEquiv :
    (𝓞 D.L ⧸ D.w.asIdeal) ≃+* D.residue :=
  (Ideal.quotEquivOfEq D.reduction_ker.symm).trans
    (D.reduction.quotientKerEquivOfSurjective D.reduction_surjective)

theorem LocalTameStage.residueEquiv_apply (x : 𝓞 D.L) :
    D.residueEquiv (Ideal.Quotient.mk D.w.asIdeal x) = D.reduction x := rfl

def LocalTameStage.inertiaResidue : Ine (F := K) A →* D.residueˣ :=
  (Units.map D.residueEquiv.toRingHom.toMonoidHom).comp
    ((finiteCompletionUnitReduction D.w).comp
      ((localArtinOnInertia D.artin_law).comp D.inertiaEquiv.symm.toMonoidHom))

theorem LocalTameStage.inertiaResidue_surjective : Function.Surjective D.inertiaResidue :=
  (Units.mapEquiv D.residueEquiv.toMulEquiv).surjective.comp
    ((finiteCompletionUnitReduction_surjective D.w).comp
      ((localArtinOnInertia_surjective D.artin_law).comp D.inertiaEquiv.symm.surjective))

theorem LocalTameStage.inertiaResidue_spec : D.IsInertiaResidue D.inertiaResidue := by
  intro t s x z hs hz hx
  have he : D.inertiaEquiv s = t := Subtype.ext hs.symm
  have hs' : D.inertiaEquiv.symm t = s := (congrArg D.inertiaEquiv.symm he.symm).trans (D.inertiaEquiv.symm_apply_apply s)
  let u := localArtinOnInertia D.artin_law s
  let y := (unitsLevelZeroEquivIntegerUnits D.w u).val
  have hy : completionReduction D.w y = completionReduction D.w (toCompletedIntegers D.w x) := by
    apply (completionReduction_eq_iff D.w _ _).mpr
    rw [show (y : D.w.adicCompletion D.L) = (u.val : D.w.adicCompletion D.L) from
      unitsLevelZeroEquivIntegerUnits_val D.w u]
    exact hx
  apply Units.ext
  change D.residueEquiv (completionReduction D.w
    (unitsLevelZeroEquivIntegerUnits D.w (localArtinOnInertia D.artin_law (D.inertiaEquiv.symm t))).val) = _
  rw [hs', show (unitsLevelZeroEquivIntegerUnits D.w u).val = y from rfl,
    hy, completionReduction_toCompletedIntegers, D.residueEquiv_apply, hz]

theorem LocalTameStage.exists_residue_approximation (t : Ine (F := K) A) :
    ∃ (s : Ine (F := D.L) A) (x : 𝓞 D.L),
      D.inertiaEquiv s = t ∧
      Valued.v ((D.artin (ineIncl D.hw s) : D.w.adicCompletion D.L) -
        algebraMap D.L (D.w.adicCompletion D.L) (x : D.L)) < 1 ∧
      D.reduction x = (D.inertiaResidue t : D.residue) := by
  let s := D.inertiaEquiv.symm t
  let u := localArtinOnInertia D.artin_law s
  have hu : Valued.v (u.val : D.w.adicCompletion D.L) ≤ 1 := (mem_unitsLevel.mp u.2).1.le
  obtain ⟨x, hx⟩ := exists_int_valued_sub_lt_one D.w (u.val : D.w.adicCompletion D.L) hu
  have hs : D.inertiaEquiv s = t := D.inertiaEquiv.apply_symm_apply t
  have hx' : Valued.v ((D.artin (ineIncl D.hw s) : D.w.adicCompletion D.L) -
      algebraMap D.L (D.w.adicCompletion D.L) (x : D.L)) < 1 := hx
  have hy : completionReduction D.w (unitsLevelZeroEquivIntegerUnits D.w u).val =
      completionReduction D.w (toCompletedIntegers D.w x) := by
    apply (completionReduction_eq_iff D.w _ _).mpr
    rw [unitsLevelZeroEquivIntegerUnits_val]
    exact hx
  refine ⟨s, x, hs, hx', ?_⟩
  change D.reduction x = D.residueEquiv (completionReduction D.w (unitsLevelZeroEquivIntegerUnits D.w u).val)
  rw [hy, completionReduction_toCompletedIntegers, D.residueEquiv_apply]

theorem LocalTameStage.inertiaResidue_unique
    (r : Ine (F := K) A →* D.residueˣ) (hr : D.IsInertiaResidue r) :
    r = D.inertiaResidue := by
  ext t
  obtain ⟨s, x, hs, hx, hz⟩ := D.exists_residue_approximation t
  exact congrArg Units.val (hr t s x _ (congrArg Subtype.val hs.symm) hz hx)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.LocalTameStage.inertiaResidue_spec
#print axioms GlobalTheory.Reciprocity.LocalTameStage.inertiaResidue_unique
