import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ResidueArtinUnramified
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinFunctoriality

/-! The residue norm of inverse Artin in an unramified extension is
the residue of inverse Artin over the base. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hv : IsPlaceOver A v)

local notation "w" => finitePlaceAtAbsoluteValuation (L := L) A hv
local notation "hw" => finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A hv

theorem residueArtinOnBaseInertia_norm
    {α : Weil hv →* (v.adicCompletion K)ˣ} (hα : IsLocalArtin K Ω (h := hv) α)
    {β : Weil hw →* ((w).adicCompletion L)ˣ} (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1) (t : Ine (F := K) A) :
    letI : (w).asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
    finiteCompletionUnitReduction v (localArtinOnInertia hα t) =
      Units.map (Algebra.norm (𝓞 K ⧸ v.asIdeal)) (residueArtinOnBaseInertia K Ω L hv hβ he t) := by
  letI : (w).asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
  let e := inertiaIsoOfUnramifiedCompletion K Ω L hv he
  let s := e.symm t
  have hs : weilRestrictScalars hv hw (ineIncl hw s) = ineIncl hv t := by
    rw [weilRestrictScalars_ineIncl]
    exact congrArg (ineIncl hv) (e.apply_symm_apply t)
  let u := (unitsLevelZeroEquivIntegerUnits v (localArtinOnInertia hα t)).val
  let z := (unitsLevelZeroEquivIntegerUnits w (localArtinOnInertia hβ s)).val
  have hu : u = completedIntegerNorm v w z := by
    apply Subtype.ext
    have hh := localArtin_weilRestrictScalars_norm K Ω L hα hβ (ineIncl hw s)
    rw [hs] at hh
    exact congrArg (fun a : (v.adicCompletion K)ˣ => (a : v.adicCompletion K)) hh
  apply Units.ext
  change completionReduction v u = Algebra.norm (𝓞 K ⧸ v.asIdeal) (completionReduction w z)
  rw [hu, completionReduction_norm_of_unramified v w he]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.residueArtinOnBaseInertia_norm
