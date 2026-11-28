import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SaturatedCompletionStage
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteWeilRestriction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.WeilCharacterFiniteStage
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SaturatedWeilRestriction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CompatibilityOfAbsoluteCentres
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalArtinInertiaImage

/-! A finite-exponent smooth Weil character over a base with the required
roots of unity factors through a global abelian stage. Its fixed field
in a finite completion lies in the full local radical field. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GlobalTheory.Kummer
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped IsMulCommutative Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

theorem finite_exponent_weilCharacter_eq_one_of_toMaxAb_eq_one_of_rootsOfUnity
    {H : Type*} [CommGroup H] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    (h : IsPlaceOver A v) (ξ : Weil h →* H) (hpow : ∀ s, ξ s ^ n = 1)
    (hop : IsOpen {s : Ine (F := K) A | ξ (ineIncl h s) = 1})
    {s : Weil h} (hs : toMaxAb K Ω (s : Gal(Ω/K)) = 1) : ξ s = 1 := by
  obtain ⟨T, hT, hgT, hξ⟩ :=
    exists_finiteGaloisStage_in_weilCharacter_ker K Ω h ξ (NeZero.pos n) hpow hop
  letI := hT
  letI := hgT
  obtain ⟨V, E, hE, hEp, hErank⟩ := exists_saturated_completion_stage K Ω (n := n) v
  let L := (V : IntermediateField K Ω)
  letI := V.2.1
  letI := V.2.2
  letI := hE
  letI : NumberField E := NumberField.of_module_finite K E
  let B := IntermediateField.lift E
  let eB : E ≃ₐ[K] B := IntermediateField.liftAlgEquiv E
  letI : FiniteDimensional K B := FiniteDimensional.of_injective eB.symm.toLinearMap eB.symm.injective
  letI : IsAbelianGalois K B := IsAbelianGalois.of_algHom eB.symm.toAlgHom
  let M := T ⊔ B
  letI : FiniteDimensional K M := inferInstance
  letI : IsGalois K M := inferInstance
  letI : NumberField M := NumberField.of_module_finite K M
  let j := (IntermediateField.inclusion (show B ≤ M from le_sup_right)).comp eB.toAlgHom
  letI : Algebra E M := j.toRingHom.toAlgebra
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let i := L.val.comp E.val
  letI : Algebra E Ω := i.toRingHom.toAlgebra
  letI : IsScalarTower K E Ω := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have hEM (x : E) : algebraMap M Ω (algebraMap E M x) = algebraMap E Ω x := rfl
  let u := finitePlaceAtAbsoluteValuation (L := E) A h
  let w := finitePlaceAtAbsoluteValuation (L := M) A h
  letI : u.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver A h
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver A h
  letI : w.asIdeal.LiesOver u.asIdeal :=
    liesOver_of_compatible_absolute_centres
      (finitePlaceAtAbsoluteValuation_isPlaceOver (K := K) (L := E) A h)
      (finitePlaceAtAbsoluteValuation_isPlaceOver (K := K) (L := M) A h) hEM
  let r := finiteWeilRestriction (L := M) h
  have hr : Function.Surjective r := finiteWeilRestriction_surjective h
  have hker : r.ker ≤ ξ.ker := by
    intro t ht
    apply MonoidHom.mem_ker.mpr
    apply hξ t
    apply MonoidHom.mem_ker.mp
    rw [T.restrictNormalHom_ker]
    apply T.fixingSubgroup_antitone (show T ≤ M from le_sup_left)
    rw [← M.restrictNormalHom_ker]
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
  let ψ := r.liftOfSurjective hr ⟨ξ, hker⟩
  have hψ (t : Weil h) : ψ (r t) = ξ t :=
    r.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hr) ⟨ξ, hker⟩ t
  have hψpow (τ : MulAction.stabilizer Gal(M/K) w.asIdeal) : ψ τ ^ n = 1 := by
    obtain ⟨t, rfl⟩ := hr τ
    rw [hψ]
    exact hpow t
  have hsfix : (s : Gal(Ω/K)) ∈ (maximalAbelianExtension K Ω).fixingSubgroup := by
    rw [← (maximalAbelianExtension K Ω).restrictNormalHom_ker]
    exact MonoidHom.mem_ker.mpr hs
  have he (x : E) : (r s).val (algebraMap E M x) = algebraMap E M x := by
    apply (algebraMap M Ω).injective
    have hx (y : M) : algebraMap M Ω ((r s).val y) = (s : Gal(Ω/K)) (algebraMap M Ω y) :=
      AlgEquiv.restrictNormal_commutes (s : Gal(Ω/K)) M y
    rw [hx, hEM]
    exact ((maximalAbelianExtension K Ω).mem_fixingSubgroup_iff _).mp hsfix _
      (le_maximalAbelianExtension B (eB x).2)
  letI : Finite (PowerClasses (v.adicCompletion K) n) := finite_finiteCompletionPowerClasses (n := n) v
  have heq := decompositionCharacter_eq_one_of_saturated_completion v u w hEp
    (hErank u) ψ hψpow (r s) he
  rwa [hψ] at heq

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finite_exponent_weilCharacter_eq_one_of_toMaxAb_eq_one_of_rootsOfUnity
