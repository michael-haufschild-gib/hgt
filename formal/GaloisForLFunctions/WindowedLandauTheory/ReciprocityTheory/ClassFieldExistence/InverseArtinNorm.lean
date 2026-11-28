import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalArtinNormFunctoriality
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InverseArtinOnWeilGroup
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicNormSinglePlace
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbsoluteWeilBaseChange
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbelianDescentFromInvariantFactor

/-! Under abelian base change, inverse Artin on the Weil group is
compatible with the local norm. An inertia element killed by global
abelianization lifts to inertia over the new base. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
  [w.asIdeal.LiesOver v.asIdeal] {hv : IsPlaceOver A v} {hw : IsPlaceOver A w}

theorem inverseArtin_weilRestrictScalars_eq_norm
    (a : CompactIdeleClassQuotient K →* Gal(maximalAbelianExtension K Ω/K))
    (b : CompactIdeleClassQuotient L →* Gal(maximalAbelianExtension L Ω/L))
    (hca : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a) (hb : MatchesFiniteIdelicArtin L Ω b)
    (α : Weil hv →* (v.adicCompletion K)ˣ) (β : Weil hw →* (w.adicCompletion L)ˣ)
    (hα : ∀ s : Weil hv, a (toCompactIdeleClassQuotient K (finiteEmbedding v (α s))) =
      toMaxAb K Ω (s : Gal(Ω/K)))
    (hβ : ∀ s : Weil hw, b (toCompactIdeleClassQuotient L (finiteEmbedding w (β s))) =
      toMaxAb L Ω (s : Gal(Ω/L)))
    (s : Weil hw) :
    α (weilRestrictScalars hv hw s) =
      Units.map (Algebra.norm (v.adicCompletion K)) (β s) := by
  apply globalArtin_injective_finiteEmbedding a hca ha v
  change a (toCompactIdeleClassQuotient K (finiteEmbedding v (α (weilRestrictScalars hv hw s)))) =
    a (toCompactIdeleClassQuotient K (finiteEmbedding v
      (Units.map (Algebra.norm (v.adicCompletion K)) (β s))))
  let w' : finitePlacesAbove L v := ⟨w, (mem_finitePlacesAbove L v w).mpr inferInstance⟩
  rw [hα, ← ideleNorm_finiteEmbedding v w']
  exact (globalArtin_ideleNorm_eq_toMaxAb K Ω L a b ha hb
    (finiteEmbedding w (β s)) s.val (hβ s)).symm

omit [FiniteDimensional K L] [IsAlgClosure L Ω] in
theorem exists_inertiaRestrictScalars_of_toMaxAb_eq_one
    (s : Ine (F := K) A) (hs : toMaxAb K Ω s.val = 1) :
    ∃ t : Ine (F := L) A, inertiaRestrictScalars t = s := by
  let r : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  have hr : s.val ∈ r.ker := by
    change s.val ∈ (AlgEquiv.restrictNormalHom L).ker
    rw [L.restrictNormalHom_ker]
    apply L.fixingSubgroup_antitone (le_maximalAbelianExtension L)
    rw [← (maximalAbelianExtension K Ω).restrictNormalHom_ker]
    exact MonoidHom.mem_ker.mpr hs
  let t := restrictionKernelEquiv K L Ω ⟨s.val, hr⟩
  have ht : t ∈ Ine (F := L) A := ⟨mem_Dec.mpr (mem_Dec.mp s.2.1), s.2.2⟩
  exact ⟨⟨t, ht⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.inverseArtin_weilRestrictScalars_eq_norm
#print axioms GlobalTheory.Reciprocity.exists_inertiaRestrictScalars_of_toMaxAb_eq_one
