import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStageIndependence
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStageSystem
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ResidueArtinNormPower
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicUnitReduction

/-! The norm of the inertia residue class agrees with base inverse
Artin. Prove it on an unramified abelian stage and transfer it
through the residue equivalence for arbitrary stages. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}
  {p n : ℕ} [Fact p.Prime]
  {α : Weil h →* (v.adicCompletion K)ˣ} (hα : IsLocalArtin K Ω α)

private theorem exists_localTameStage_with_norm_pow
    (i : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i) (hn : 0 < n)
    (e : (𝓞 K ⧸ v.asIdeal) ≃+* ZMod p) :
    ∃ D : LocalTameStage h p n, ∀ t : Ine (F := K) A,
      algebraMap (ZMod p) D.residue (e (finiteCompletionUnitReduction v (localArtinOnInertia hα t))) =
        ∏ j ∈ Finset.range n, ((D.inertiaResidue t ^ p ^ j : D.residueˣ) : D.residue) := by
  obtain ⟨S, he, hc, hp, hp'⟩ := exists_unramified_padicStage K Ω h i hi hn
  let L := (S : IntermediateField K Ω)
  letI : FiniteDimensional K L := S.2.1
  letI : IsAbelianGalois K L := S.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) L⟩
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  let hw := finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A h
  obtain ⟨β, hβ, -⟩ := existsUnique_localArtin L Ω hw
  let D : LocalTameStage h p n := LocalTameStage.ofQuotient hw hp hp' hc β hβ
  refine ⟨D, fun t => ?_⟩
  let j := inertiaIsoOfUnramifiedCompletion K Ω L h he
  have hj : D.inertiaEquiv.symm t = j.symm t :=
    D.inertiaEquiv.injective ((D.inertiaEquiv.apply_symm_apply t).trans (j.apply_symm_apply t).symm)
  have hE (x : 𝓞 L ⧸ w.asIdeal) : D.residueEquiv x = x := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact D.residueEquiv_apply y
  let r := residueArtinOnBaseInertia K Ω L h hβ he
  have hr : D.inertiaResidue t = r t := by
    apply Units.ext
    change D.residueEquiv (finiteCompletionUnitReduction w
      (localArtinOnInertia hβ (D.inertiaEquiv.symm t)) : 𝓞 L ⧸ w.asIdeal) =
        (finiteCompletionUnitReduction w (localArtinOnInertia hβ (j.symm t)) : 𝓞 L ⧸ w.asIdeal)
    rw [hE, hj]
  letI : Algebra (ZMod p) (𝓞 L ⧸ w.asIdeal) := D.primeAlgebra
  have hn' := D.residue_rank
  rw [hr]
  exact residueArtinOnBaseInertia_norm_pow K Ω L h e hn' hα hβ he t

theorem LocalTameStage.inertiaResidue_norm_pow (D : LocalTameStage h p n)
    (i : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i) (hn : 0 < n)
    (e : (𝓞 K ⧸ v.asIdeal) ≃+* ZMod p) (t : Ine (F := K) A) :
    algebraMap (ZMod p) D.residue (e (finiteCompletionUnitReduction v (localArtinOnInertia hα t))) =
      ∏ j ∈ Finset.range n, ((D.inertiaResidue t ^ p ^ j : D.residueˣ) : D.residue) := by
  obtain ⟨D', hD'⟩ := exists_localTameStage_with_norm_pow hα i hi hn e
  obtain ⟨f, hf⟩ := exists_residueEquiv_intertwining_inertiaResidue D' D
  have hmap : f.toRingHom.comp (algebraMap (ZMod p) D'.residue) = algebraMap (ZMod p) D.residue :=
    RingHom.ext_zmod _ _
  have hu := congrArg f (hD' t)
  rw [map_prod] at hu
  change (f.toRingHom.comp (algebraMap (ZMod p) D'.residue))
    (e (finiteCompletionUnitReduction v (localArtinOnInertia hα t))) = _ at hu
  rw [hmap] at hu
  rw [hu]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hf t, ← map_pow (Units.map f.toRingHom.toMonoidHom)]
  rfl

include hα in
theorem LocalTameStage.base_artin_unit (D : LocalTameStage h p n)
    (r : Ine (F := K) A →* D.residueˣ) (hr : D.IsInertiaResidue r)
    (i : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i) (hn : 0 < n)
    (t : Ine (F := K) A) :
    ∃ z : ℤ_[p]ˣ, (α (ineIncl h t) : v.adicCompletion K) = i (z.val : ℚ_[p]) ∧
      algebraMap (ZMod p) D.residue (PadicInt.toZMod z.val) =
        ∏ j ∈ Finset.range n, ((r t ^ p ^ j : D.residueˣ) : D.residue) := by
  obtain ⟨e, he⟩ := exists_padic_residue_equiv_of_completion v i hi
  obtain ⟨z, hz, hzr⟩ := he (localArtinOnInertia hα t)
  refine ⟨z, hz, ?_⟩
  rw [D.inertiaResidue_unique r hr, ← D.inertiaResidue_norm_pow hα i hi hn e t]
  exact congrArg (algebraMap (ZMod p) D.residue) (congrArg Units.val hzr).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.LocalTameStage.base_artin_unit
