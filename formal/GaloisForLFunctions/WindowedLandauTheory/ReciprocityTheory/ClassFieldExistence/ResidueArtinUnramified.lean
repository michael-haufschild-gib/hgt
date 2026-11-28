import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InertiaBaseChangeUnramified
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.TameArtinCharacters

/-! At a finite place with an unramified extension, residue reduction
of local Artin on inertia is surjective, has open kernel, and kills
wild inertia. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory.TameKummer
open scoped Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hv : IsPlaceOver A v)

local notation "w" => finitePlaceAtAbsoluteValuation (L := L) A hv
local notation "hw" => finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A hv

/-- Inverse Artin on the inertia of the base, valued in the units of
an unramified completion. -/
def unitArtinOnBaseInertia {β : Weil hw →* ((w).adicCompletion L)ˣ}
    (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1) :
    Ine (F := K) A →* unitsLevel (K := L) w 0 :=
  (localArtinOnInertia hβ).comp (inertiaIsoOfUnramifiedCompletion K Ω L hv he).symm.toMonoidHom

theorem unitArtinOnBaseInertia_surjective {β : Weil hw →* ((w).adicCompletion L)ˣ}
    (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1) :
    Function.Surjective (unitArtinOnBaseInertia K Ω L hv hβ he) :=
  (localArtinOnInertia_surjective hβ).comp (inertiaIsoOfUnramifiedCompletion K Ω L hv he).symm.surjective

theorem continuous_unitArtinOnBaseInertia {β : Weil hw →* ((w).adicCompletion L)ˣ}
    (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1) :
    Continuous (unitArtinOnBaseInertia K Ω L hv hβ he) :=
  (continuous_localArtinOnInertia hβ).comp (continuous_inertiaIsoOfUnramifiedCompletion_symm K Ω L hv he)

/-- Residue reduction of inverse Artin on base inertia. -/
def residueArtinOnBaseInertia {β : Weil hw →* ((w).adicCompletion L)ˣ}
    (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1) :
    Ine (F := K) A →* (𝓞 L ⧸ (w).asIdeal)ˣ :=
  (finiteCompletionUnitReduction w).comp (unitArtinOnBaseInertia K Ω L hv hβ he)

theorem residueArtinOnBaseInertia_surjective {β : Weil hw →* ((w).adicCompletion L)ˣ}
    (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1) :
    Function.Surjective (residueArtinOnBaseInertia K Ω L hv hβ he) :=
  (finiteCompletionUnitReduction_surjective w).comp (unitArtinOnBaseInertia_surjective K Ω L hv hβ he)

theorem residueArtinOnBaseInertia_open_ker
    {β : Weil hw →* ((w).adicCompletion L)ˣ} (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1) :
    IsOpen ((residueArtinOnBaseInertia K Ω L hv hβ he).ker : Set (Ine (F := K) A)) := by
  let e := inertiaIsoOfUnramifiedCompletion K Ω L hv he
  have hc := (hβ.cont.comp (continuous_inertiaIsoOfUnramifiedCompletion_symm K Ω L hv he))
  have hset : ((residueArtinOnBaseInertia K Ω L hv hβ he).ker : Set (Ine (F := K) A)) =
      (fun t => β (ineIncl hw (e.symm t))) ⁻¹' (unitsLevel (K := L) w 1 : Set ((w).adicCompletion L)ˣ) := by
    ext t
    exact (finiteCompletionUnitReduction_eq_one_iff w (localArtinOnInertia hβ (e.symm t))).trans
      (mem_unitsLevel_one_iff_lt_one w _).symm
  rw [hset]
  exact (isOpen_unitsLevel (K := L) w 1).preimage hc

theorem residueArtinOnBaseInertia_wild {β : Weil hw →* ((w).adicCompletion L)ˣ}
    (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1)
    (t : Ine (F := K) A) (ht : t.val ∈ wildInertia A) :
    residueArtinOnBaseInertia K Ω L hv hβ he t = 1 := by
  let e := inertiaIsoOfUnramifiedCompletion K Ω L hv he
  let s := e.symm t
  have ht' : inertiaRestrictScalars (K := K) (L := L) (A := A) s = t := e.apply_symm_apply t
  have hs' (x : Ω) : s.val x = t.val x :=
    congrArg (fun z : Ine (F := K) A => z.val x) ht'
  have hs : s.val ∈ wildInertia A := (mem_wildInertia_iff _ _).mpr fun x hx => by
    rw [hs' x]
    exact (mem_wildInertia_iff _ _).mp ht x hx
  have hf := artin_mem_unitsLevel_one_of_mem_wildInertia hβ (ineIncl hw s) hs
  apply (finiteCompletionUnitReduction_eq_one_iff w (localArtinOnInertia hβ s)).mpr
  exact (mem_unitsLevel_one_iff_lt_one w _).mp hf

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.residueArtinOnBaseInertia_wild
#print axioms GlobalTheory.Reciprocity.residueArtinOnBaseInertia_open_ker
