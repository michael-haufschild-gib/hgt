import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePlaceOfAbsoluteValuation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbsoluteWeilBaseChange

/-! In a finite extension unramified at the selected place, absolute
inertia fixes the extension. In the normal closure the two inertia
groups have the same order by ramification transitivity. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : Type) [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)

theorem absoluteInertia_fixes_of_unramified_extension
    (he : (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal.ramificationIdx (𝓞 K) = 1)
    (t : Ine (F := K) A) (x : L) :
    t.val (algebraMap L Ω x) = algebraMap L Ω x := by
  let M := normalClosure K L Ω
  letI : FiniteDimensional K M := normalClosure.is_finiteDimensional K L Ω
  letI : IsGalois K M := IsGalois.normalClosure K L Ω
  letI : NumberField M := NumberField.of_module_finite K M
  letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  let hw := finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A h
  let W := finitePlaceAtAbsoluteValuation (L := M) A h
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  letI : W.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := M) A h
  letI : W.asIdeal.LiesOver w.asIdeal := by
    have hW : W = finitePlaceAtAbsoluteValuation (L := M) A hw := HeightOneSpectrum.ext rfl
    rw [hW]
    exact finitePlaceAtAbsoluteValuation_liesOver (L := M) A hw
  let I := W.asIdeal.inertia Gal(M/K)
  let J := W.asIdeal.inertia Gal(M/L)
  let r : J → I := fun s =>
    ⟨s.val.restrictScalars K, AddSubgroup.mem_inertia.mpr
      (fun y => AddSubgroup.mem_inertia.mp s.2 y)⟩
  have hi : Function.Injective r := fun a b hab =>
    Subtype.ext (AlgEquiv.restrictScalars_injective K (congrArg Subtype.val hab))
  have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal W.asIdeal
  rw [show w.asIdeal.ramificationIdx (𝓞 K) = 1 from he, one_mul] at htower
  letI := v.isMaximal
  letI := w.isMaximal
  letI := W.isMaximal
  have hI : Nat.card I = W.asIdeal.ramificationIdx (𝓞 K) := by
    change Nat.card (W.asIdeal.inertia Gal(M/K)) = _
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(M/K)) v.asIdeal W.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal W.asIdeal Gal(M/K)]
  have hJ : Nat.card J = W.asIdeal.ramificationIdx (𝓞 L) := by
    change Nat.card (W.asIdeal.inertia Gal(M/L)) = _
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(M/L)) w.asIdeal W.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal W.asIdeal Gal(M/L)]
  have hs : Function.Surjective r := (hi.bijective_of_nat_card_le (by rw [hI, hJ, htower])).2
  let a := AlgEquiv.restrictNormalHom M t.val
  have ha : a ∈ I := restrictNormalHom_mem_inertia_of_mem_Ine A h t.2
  obtain ⟨b, hb⟩ := hs ⟨a, ha⟩
  have hb' : b.val.restrictScalars K = a := congrArg Subtype.val hb
  change t.val (algebraMap L Ω x) = algebraMap L Ω x
  rw [IsScalarTower.algebraMap_apply L M Ω, ← AlgEquiv.restrictNormal_commutes t.val M]
  change algebraMap M Ω (a (algebraMap L M x)) = _
  rw [← hb']
  exact congrArg (algebraMap M Ω) (b.val.commutes x)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.absoluteInertia_fixes_of_unramified_extension
