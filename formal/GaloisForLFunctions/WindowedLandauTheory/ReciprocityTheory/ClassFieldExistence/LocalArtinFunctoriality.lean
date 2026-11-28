import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinData
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InverseArtinEquivariance
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InverseArtinNorm

/-! Geometrically normalized inverse Artin commutes with local norms
under restriction and with decomposition automorphisms under conjugation. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
  [w.asIdeal.LiesOver v.asIdeal] {hv : IsPlaceOver A v} {hw : IsPlaceOver A w}

theorem localArtin_weilRestrictScalars_norm
    {α : Weil hv →* (v.adicCompletion K)ˣ} {β : Weil hw →* (w.adicCompletion L)ˣ}
    (hα : IsLocalArtin K Ω α) (hβ : IsLocalArtin L Ω β)
    (s : Weil hw) :
    α (weilRestrictScalars hv hw s) = Units.map (Algebra.norm (v.adicCompletion K)) (β s) := by
  obtain ⟨a, hca, ha, -⟩ := exists_global_idelic_artin K Ω
  obtain ⟨b, -, hb, -⟩ := exists_global_idelic_artin L Ω
  have he := inverseArtin_weilRestrictScalars_eq_norm K Ω L a b hca ha hb
    α⁻¹ β⁻¹ (hα.glob a ha) (hβ.glob b hb) s
  change (α (weilRestrictScalars hv hw s))⁻¹ =
    Units.map (Algebra.norm (v.adicCompletion K)) ((β s)⁻¹) at he
  rw [map_inv] at he
  exact inv_injective he

theorem localArtin_conjugateWeil
    {β : Weil hw →* (w.adicCompletion L)ˣ} (hβ : IsLocalArtin L Ω β)
    (t : Weil hv) (s : Weil hw)
    (ht : AlgEquiv.restrictNormalHom L t.val ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) :
    β (conjugateWeil K Ω L t s) =
      Units.map (decompositionMulEquiv v w ⟨AlgEquiv.restrictNormalHom L t.val, ht⟩).toMonoidHom (β s) := by
  obtain ⟨b, hcb, hb, -⟩ := exists_global_idelic_artin L Ω
  have he := inverseArtin_conjugateWeil K Ω L b hcb hb β⁻¹ (hβ.glob b hb) t s ht
  change (β (conjugateWeil K Ω L t s))⁻¹ =
    Units.map (decompositionMulEquiv v w ⟨AlgEquiv.restrictNormalHom L t.val, ht⟩).toMonoidHom ((β s)⁻¹) at he
  rw [map_inv] at he
  exact inv_injective he

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.localArtin_weilRestrictScalars_norm
#print axioms GlobalTheory.Reciprocity.localArtin_conjugateWeil
