import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InverseArtinEquivariance
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteWeilRestriction
import GaloisForLFunctions.HTGeometry.ABHN.CyclicHilbert90

/-! Across a finite cyclic extension, a Weil character descending by
local Artin over the upper field descends over the base. Conjugation
invariance and cyclic Hilbert 90 kill the kernel of the local norm. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ABHN
open scoped Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L] [IsCyclic Gal(L/K)]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hv : IsPlaceOver A v)

theorem weilCharacter_eq_one_of_toMaxAb_eq_one_of_cyclic_descent
    {H : Type*} [CommGroup H] (ξ : Weil hv →* H)
    (hL : let hw := finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A hv
          letI : (finitePlaceAtAbsoluteValuation (L := L) A hv).asIdeal.LiesOver v.asIdeal :=
            finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
          ∀ s : Weil hw, toMaxAb L Ω (s : Gal(Ω/L)) = 1 → ξ (weilRestrictScalars hv hw s) = 1)
    {s : Weil hv} (hs : toMaxAb K Ω (s : Gal(Ω/K)) = 1) : ξ s = 1 := by
  let w := finitePlaceAtAbsoluteValuation (L := L) A hv
  let hw : IsPlaceOver A w := finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A hv
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
  let F := v.adicCompletion K
  let P := w.adicCompletion L
  obtain ⟨a, hca, ha, -⟩ := exists_global_idelic_artin K Ω
  obtain ⟨b, hcb, hb, -⟩ := exists_global_idelic_artin L Ω
  obtain ⟨α, -, hαd, hα⟩ := exists_inverse_arithmeticArtin_on_Weil K Ω a hca ha hv
  obtain ⟨β, hβs, -, hβ⟩ := exists_inverse_arithmeticArtin_on_Weil L Ω b hcb hb hw
  let j := weilRestrictScalars hv hw
  have hker : β.ker ≤ (ξ.comp j).ker := by
    intro z hz
    apply MonoidHom.mem_ker.mpr
    apply hL z
    rw [← hβ z, MonoidHom.mem_ker.mp hz, map_one, map_one, map_one]
  let χ := β.liftOfSurjective hβs ⟨ξ.comp j, hker⟩
  have hχ (z : Weil hw) : χ (β z) = ξ (j z) :=
    β.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hβs) ⟨ξ.comp j, hker⟩ z
  let D := MulAction.stabilizer Gal(L/K) w.asIdeal
  let e := decompositionMulEquiv v w
  have hinv (g : Gal(P/F)) (x : Pˣ) : χ (Units.map g.toMonoidHom x) = χ x := by
    obtain ⟨u, rfl⟩ := e.surjective g
    obtain ⟨t, ht⟩ := finiteWeilRestriction_surjective (L := L) hv u
    obtain ⟨z, rfl⟩ := hβs x
    let ht₀ : AlgEquiv.restrictNormalHom L t.val ∈ D :=
      restrictNormalHom_mem_stabilizer_of_mem_Dec A hv (Weil_le_Dec hv t.2)
    have hu : (⟨AlgEquiv.restrictNormalHom L t.val, ht₀⟩ : D) = u := ht
    rw [← hu, ← inverseArtin_conjugateWeil K Ω L b hcb hb β hβ t z ht₀, hχ, hχ]
    change ξ (weilRestrictScalars hv hw (conjugateWeil K Ω L t z)) = ξ (j z)
    rw [weilRestrictScalars_conjugateWeil, map_mul, map_mul, map_inv, mul_comm (ξ t),
      mul_inv_cancel_right]
  have hαs : α s = 1 := by
    apply globalArtin_injective_finiteEmbedding a hca ha v
    change a (toCompactIdeleClassQuotient K (finiteEmbedding v (α s))) =
      a (toCompactIdeleClassQuotient K (finiteEmbedding v 1))
    rw [hα, hs, map_one, map_one, map_one]
  have hd : deg s = 0 := by
    have he := hαd s
    rw [hαs, map_one] at he
    exact Multiplicative.ofAdd.injective he.symm
  let z : Ine (F := K) A := ⟨s.val, deg_eq_zero_iff.mp hd⟩
  obtain ⟨z', hz'⟩ := exists_inertiaRestrictScalars_of_toMaxAb_eq_one K Ω L z hs
  let u := ineIncl hw z'
  have hu : j u = s := by
    change weilRestrictScalars hv hw (ineIncl hw z') = s
    rw [weilRestrictScalars_ineIncl, hz']
    exact Subtype.ext rfl
  have hN := inverseArtin_weilRestrictScalars_eq_norm K Ω L a b hca ha hb α β hα hβ u
  change α (j u) = _ at hN
  rw [hu, hαs] at hN
  letI : IsCyclic D := isCyclic_of_injective D.subtype Subtype.val_injective
  letI : IsCyclic Gal(P/F) := e.isCyclic.mp inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(P/F))
  obtain ⟨y, hy⟩ := (cyclicGalois_hilbert90_exact hg (Additive.ofMul (β u))).mp
    (congrArg Additive.ofMul hN.symm)
  have he : Additive.toMul y / Units.map g.toMonoidHom (Additive.toMul y) = β u :=
    congrArg Additive.toMul hy
  rw [← hu, ← hχ, ← he, map_div, hinv, div_self']

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.weilCharacter_eq_one_of_toMaxAb_eq_one_of_cyclic_descent
