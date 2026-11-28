import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbsoluteWeilBaseChange
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePlaceOfAbsoluteValuation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbelianDescentFromInvariantFactor

/-! At the selected unramified place, restriction of scalars is an
isomorphism on absolute inertia, with continuous inverse. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] [NumberField L]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)

theorem inertiaRestrictScalars_bijective_of_unramified
    (he : (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal.ramificationIdx (𝓞 K) = 1) :
    Function.Bijective (inertiaRestrictScalars (K := K) (L := L) (A := A)) := by
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  letI := w.isMaximal
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  have hI := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K), he] at hI
  letI : Subsingleton (w.asIdeal.inertia Gal(L/K)) := (Nat.card_eq_one_iff_unique.mp hI).1
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply AlgEquiv.restrictScalars_injective K
    exact congrArg Subtype.val hxy
  · intro t
    let r : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
    have hr : r t.val ∈ w.asIdeal.inertia Gal(L/K) :=
      restrictNormalHom_mem_inertia_of_mem_Ine A h t.2
    have hrt : r t.val = 1 := congrArg Subtype.val
      (Subsingleton.elim (⟨r t.val, hr⟩ : w.asIdeal.inertia Gal(L/K)) 1)
    let s := restrictionKernelEquiv K L Ω ⟨t.val, MonoidHom.mem_ker.mpr hrt⟩
    have hs : s ∈ Ine (F := L) A := ⟨mem_Dec.mpr (mem_Dec.mp t.2.1), t.2.2⟩
    exact ⟨⟨s, hs⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩

def inertiaIsoOfUnramifiedCompletion
    (he : (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal.ramificationIdx (𝓞 K) = 1) :
    Ine (F := L) A ≃* Ine (F := K) A :=
  MulEquiv.ofBijective (inertiaRestrictScalars (K := K) (L := L) (A := A))
    (inertiaRestrictScalars_bijective_of_unramified K Ω L h he)

theorem continuous_inertiaIsoOfUnramifiedCompletion_symm [IsAlgClosure L Ω]
    (he : (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal.ramificationIdx (𝓞 K) = 1) :
    Continuous (inertiaIsoOfUnramifiedCompletion K Ω L h he).symm := by
  letI := compactSpace_Ine (E := L) A
  letI : T2Space Gal(Ω/K) := krullTopology_t2
  let e := (inertiaIsoOfUnramifiedCompletion K Ω L h he).toEquiv
  have hc : Continuous e := continuous_inertiaRestrictScalars (K := K) (L := L) (A := A)
  exact (hc.homeoOfEquivCompactToT2 (f := e)).symm.continuous

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.inertiaRestrictScalars_bijective_of_unramified
#print axioms GlobalTheory.Reciprocity.continuous_inertiaIsoOfUnramifiedCompletion_symm
