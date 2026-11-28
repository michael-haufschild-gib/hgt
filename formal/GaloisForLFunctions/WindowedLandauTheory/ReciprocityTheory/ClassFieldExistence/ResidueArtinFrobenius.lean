import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ResidueArtinUnramified
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionResidueFrobenius
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinFunctoriality

/-! On the residue of an unramified stage, inverse Artin intertwines
Frobenius conjugation with the residue-cardinality power. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory.TameKummer
open scoped Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

private theorem finiteCompletionUnitReduction_decomposition_frobenius
    {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (σ : MulAction.stabilizer Gal(E/K) w.asIdeal)
    (hσ : IsArithFrobAt (𝓞 K) σ.val w.asIdeal)
    (x y : unitsLevel (K := E) w 0)
    (hy : y.val = Units.map (decompositionMulEquiv v w σ).toMonoidHom x.val) :
    finiteCompletionUnitReduction w y = finiteCompletionUnitReduction w x ^ normV v := by
  let u := (unitsLevelZeroEquivIntegerUnits w x).val
  let z := (unitsLevelZeroEquivIntegerUnits w y).val
  have h : z = decompositionOnCompletedIntegersEquiv v w σ u := by
    apply Subtype.ext
    change (z : w.adicCompletion E) = decompositionMulEquiv v w σ (u : w.adicCompletion E)
    rw [show (z : w.adicCompletion E) = (y.val : w.adicCompletion E) from
      unitsLevelZeroEquivIntegerUnits_val w y,
      show (u : w.adicCompletion E) = (x.val : w.adicCompletion E) from
      unitsLevelZeroEquivIntegerUnits_val w x]
    exact congrArg (fun a : (w.adicCompletion E)ˣ => (a : w.adicCompletion E)) hy
  apply Units.ext
  change completionReduction w z = (completionReduction w u) ^ normV v
  rw [h, completionReduction_decomposition_frobenius v w σ hσ]

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hv : IsPlaceOver A v)

local notation "w" => finitePlaceAtAbsoluteValuation (L := L) A hv
local notation "hw" => finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A hv

theorem unitArtinOnBaseInertia_conjugation {β : Weil hw →* ((w).adicCompletion L)ˣ}
    (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1)
    (φ : Weil hv) (t t' : Ine (F := K) A)
    (ht : ineIncl hv t' = φ * ineIncl hv t * φ⁻¹)
    (hσ : AlgEquiv.restrictNormalHom L φ.val ∈ MulAction.stabilizer Gal(L/K) (w).asIdeal) :
    letI : (w).asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
    (unitArtinOnBaseInertia K Ω L hv hβ he t').val =
      Units.map (decompositionMulEquiv v w ⟨AlgEquiv.restrictNormalHom L φ.val, hσ⟩).toMonoidHom
        (unitArtinOnBaseInertia K Ω L hv hβ he t).val := by
  letI : (w).asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
  let e := inertiaIsoOfUnramifiedCompletion K Ω L hv he
  let s := e.symm t
  let s' := e.symm t'
  have hrestrict (u : Ine (F := K) A) :
      weilRestrictScalars hv hw (ineIncl hw (e.symm u)) = ineIncl hv u := by
    rw [weilRestrictScalars_ineIncl]
    exact congrArg (ineIncl hv) (e.apply_symm_apply u)
  have hconj : conjugateWeil K Ω L φ (ineIncl hw s) = ineIncl hw s' := by
    have hx : weilRestrictScalars hv hw (conjugateWeil K Ω L φ (ineIncl hw s)) =
        weilRestrictScalars hv hw (ineIncl hw s') := by
      rw [weilRestrictScalars_conjugateWeil, hrestrict t, hrestrict t', ht]
    apply Subtype.ext
    apply AlgEquiv.restrictScalars_injective K
    exact congrArg Subtype.val hx
  have hy := localArtin_conjugateWeil K Ω L hβ φ (ineIncl hw s) hσ
  rwa [hconj] at hy

theorem residueArtinOnBaseInertia_conjugation {β : Weil hw →* ((w).adicCompletion L)ˣ}
    (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1)
    (φ : Weil hv) (hφ : deg φ = 1) (t t' : Ine (F := K) A)
    (ht : ineIncl hv t' = φ * ineIncl hv t * φ⁻¹) :
    residueArtinOnBaseInertia K Ω L hv hβ he t' =
      residueArtinOnBaseInertia K Ω L hv hβ he t ^ normV v := by
  letI : (w).asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
  let σ := AlgEquiv.restrictNormalHom L φ.val
  have hσ : IsArithFrobAt (𝓞 K) σ (w).asIdeal :=
    restrictNormalHom_isArithFrobAt A hv (deg_eq_one_iff.mp hφ)
  have hσ' : σ ∈ MulAction.stabilizer Gal(L/K) (w).asIdeal := hσ.mem_stabilizer
  exact finiteCompletionUnitReduction_decomposition_frobenius v w ⟨σ, hσ'⟩ hσ
    (unitArtinOnBaseInertia K Ω L hv hβ he t) (unitArtinOnBaseInertia K Ω L hv hβ he t')
    (unitArtinOnBaseInertia_conjugation K Ω L hv hβ he φ t t' ht hσ')

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.unitArtinOnBaseInertia_conjugation
#print axioms GlobalTheory.Reciprocity.residueArtinOnBaseInertia_conjugation
