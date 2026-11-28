import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.TameResidueArtinCalibration
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.UnramifiedCompletionOfDegree
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InertiaBaseChangeUnramified
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinFunctoriality

/-! Tame inverse Artin agrees with reduction of the uniformizer-radical
ratio, even when the number field does not contain all roots of unity
of order one less than the residue cardinality. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField WithZero
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)

theorem residue_inverseArtin_eq_uniformizerRadical {a : Kˣ}
    (ha : Valued.v (algebraMap K (v.adicCompletion K) (a : K)) = exp (-1 : ℤ))
    (π : Ω) (hπ : π ^ (normV v - 1) = algebraMap K Ω (a : K))
    {α : Weil h →* (v.adicCompletion K)ˣ} (hα : IsLocalArtin K Ω α)
    (t : Ine (F := K) A) (x : 𝓞 K)
    (hx : Valued.v ((α (ineIncl h t) : v.adicCompletion K) -
        algebraMap K (v.adicCompletion K) (x : K)) < 1) :
    A.valuation (t.val π / π - algebraMap K Ω (x : K)) < 1 := by
  let q := normV v
  let m := q - 1
  have hq : 1 < q := one_lt_normV v
  have hmv : (m : 𝓞 K) ∉ v.asIdeal := by
    let Q := Ideal.Quotient.mk v.asIdeal
    have hq0 : Q (q : 𝓞 K) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.absNorm_mem v.asIdeal)
    intro hm
    have h0 : Q (m : 𝓞 K) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have he : (q : 𝓞 K) = (m : 𝓞 K) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hq.le).symm
    have hh := congrArg Q he
    rw [hq0, map_add, h0, map_one, zero_add] at hh
    exact zero_ne_one hh
  have hmA : ¬ A.valuation (m : Ω) < 1 := by
    intro hm
    apply hmv
    apply (h (m : 𝓞 K)).mp
    simpa only [map_natCast] using hm
  have hmV : Valued.v (m : v.adicCompletion K) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) (v.adicCompletion K))]
    exact le_antisymm (valued_algebraMap_int_le_one v _)
      (le_of_not_gt fun hc => hmv ((valued_algebraMap_int_lt_one_iff v _).mp hc))
  obtain ⟨T, he, hf, hd, hR⟩ := exists_unramified_completion_withRoots K Ω h Nat.one_pos
  let L := (T : IntermediateField K Ω)
  letI : FiniteDimensional K L := T.2.1
  letI : IsAbelianGalois K L := T.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  letI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) L⟩
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  let hw := finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A h
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  letI := v.isMaximal
  letI := w.isMaximal
  have hqpow : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K) :=
    (Ideal.cardQuot_pow_inertiaDeg v.asIdeal w.asIdeal).symm
  have hq' : normV w = normV v := by
    rw [hqpow, show w.asIdeal.inertiaDeg (𝓞 K) = 1 from hf, pow_one]
  letI : HasEnoughRootsOfUnity L (normV w - 1) := by
    rw [hq']
    simpa only [pow_one] using hR
  let F := v.adicCompletion K
  let G := w.adicCompletion L
  let j := AdicLiesOver.completionMap v w
  have hv (z : F) : Valued.v (j z) = Valued.v z := by
    rw [AdicLiesOver.valued_completionMap,
      Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot, show w.asIdeal.ramificationIdx (𝓞 K) = 1 from he, pow_one]
  have hNJ (z : G) : j (Algebra.norm F z) = z := by
    letI : Module.Free F G := Module.Free.of_divisionRing F G
    have hd' : Module.finrank F G = 1 := hd
    have hsurj : Function.Surjective (algebraMap F G) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd').2
    obtain ⟨y, rfl⟩ := hsurj z
    change algebraMap F G (Algebra.norm F (algebraMap F G y)) = _
    rw [Algebra.norm_algebraMap, hd', pow_one]
  obtain ⟨β, hβ, -⟩ := existsUnique_localArtin L Ω hw
  let e := inertiaIsoOfUnramifiedCompletion K Ω L h he
  let s := e.symm t
  have ht : weilRestrictScalars h hw (ineIncl hw s) = ineIncl h t := by
    rw [weilRestrictScalars_ineIncl]
    exact congrArg (ineIncl h) (e.apply_symm_apply t)
  have hN := localArtin_weilRestrictScalars_norm K Ω L hα hβ (ineIncl hw s)
  rw [ht] at hN
  have hβ' : j (α (ineIncl h t) : F) = (β (ineIncl hw s) : G) :=
    (congrArg j (congrArg (fun y : Fˣ => (y : F)) hN)).trans (hNJ _)
  let b := Units.map (algebraMap K L).toMonoidHom a
  let y : 𝓞 L := algebraMap (𝓞 K) (𝓞 L) x
  have hj (z : K) : j (algebraMap K F z) = algebraMap L G (algebraMap K L z) :=
    AdicLiesOver.completionMap_algebraMap v w z
  have hb : Valued.v (algebraMap L G (b : L)) = exp (-1 : ℤ) := by
    change Valued.v (algebraMap L G (algebraMap K L (a : K))) = _
    rw [← hj, hv, ha]
  have hπ' : π ^ (normV w - 1) = algebraMap L Ω (b : L) := by
    change π ^ (normV w - 1) = algebraMap L Ω (algebraMap K L (a : K))
    rw [hq', hπ, ← IsScalarTower.algebraMap_apply]
  have hmV' : Valued.v ((normV w - 1 : ℕ) : G) = 1 := by
    rw [hq', ← map_natCast j, hv]
    exact hmV
  have hy : Valued.v ((β (ineIncl hw s) : G) - algebraMap L G (y : L)) < 1 := by
    change Valued.v ((β (ineIncl hw s) : G) - algebraMap L G (algebraMap K L (x : K))) < 1
    rw [← hβ', ← hj, ← map_sub, hv]
    exact hx
  have hg := residue_inverseArtin_eq_uniformizerRadical_of_roots (h := hw)
    hb π hπ' (by rwa [hq']) hmV' hβ s y hy
  have hsπ : s.val π = t.val π :=
    congrArg (fun z : Ine (F := K) A => z.val π) (e.apply_symm_apply t)
  change A.valuation (s.val π / π - algebraMap L Ω (algebraMap K L (x : K))) < 1 at hg
  rwa [hsπ, ← IsScalarTower.algebraMap_apply] at hg

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.residue_inverseArtin_eq_uniformizerRadical
