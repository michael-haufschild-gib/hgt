import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceHigherRamification

/-!
# Completed lower profile of the actual Q8 quadratic source

The chosen source-to-completion equivalence preserves every lower congruence depth.  Consequently
the source profile transports without hidden completed automorphisms: levels zero through two are
exactly central and every level from three onward is trivial.
-/

namespace RHTower

noncomputable section

open scoped NumberField Pointwise ValuativeRel NNReal
open IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField
local notation "S" => q8BiquadQuadraticSourceField

local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst2 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst3 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst4 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst5 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst6 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst7 : FiniteDimensional S K2 := by infer_instance
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst8 : FiniteDimensional S K3 :=
  FiniteDimensional.trans S K2 K3
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst9 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst10 : NumberField S := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst11 : NumberField K2 := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst12 : NumberField K3 := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst13 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
noncomputable local instance deningerQ8ActualQuadraticSourceCompletedProfileLocalInst14 : IsGalois S K3 :=
  IsGalois.tower_top_of_isGalois ℚ S K3

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenGlobalValuationLower_le_sourceLower
    (v : HeightOneSpectrum (𝓞 S))
    (n : ℕ)
    (σ : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup S
      (q8ChosenGlobalValuationRing v))
    (hσ : ∀ x : q8ChosenGlobalValuationRing v,
      σ • x - x ∈ IsLocalRing.maximalIdeal (q8ChosenGlobalValuationRing v) ^ (n + 1)) :
    (σ : Gal(K3/S)) ∈
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S))
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)).asIdeal n := by
  let w := chosenFinitePlaceExtension (L := K3) v
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v w
  let e := q8ChosenGlobalLocalizationEquiv v
  intro x
  let xA : q8ChosenGlobalValuationRing v :=
    ringOfIntegersToFinitePlaceExtensionValuationSubring v w x
  have hxA := hσ xA
  have hmapped : e (σ • xA - xA) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ (n + 1) :=
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff e (n + 1) _).2 hxA
  have heq : e (σ • xA - xA) =
      algebraMap (𝓞 K3) (Localization.AtPrime P.asIdeal) ((σ : Gal(K3/S)) • x - x) := by
    apply q8PlaceLocalizationToTopField_injective P
    rw [q8ChosenGlobalLocalizationEquiv_toTopField]
    change (σ : Gal(K3/S)) (x : K3) - (x : K3) = _
    simp only [q8PlaceLocalizationToTopField,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      RingHom.coe_comp, ValuationSubring.coe_subtype, RingHom.coe_coe,
      Function.comp_apply, AlgEquiv.commutes]
    rfl
  rwa [heq] at hmapped

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
noncomputable def q8QuadraticSourceChosenLocalGalEquiv
    (v : HeightOneSpectrum (𝓞 S)) :
    RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup S
        (q8ChosenGlobalValuationRing v) ≃*
      Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
        ChosenFinitePlaceBaseCompletion (K := S) v) :=
  let vK := NumberField.HeightOneSpectrum.adicAbv S v
  let w := chosenFinitePlaceExtension (L := K3) v
  let hw := finitePlaceExtension_nonarchimedean (K := S) (L := K3) v w
  (localizationRamificationGroups_valuationDecompositionGroupEquiv
      vK (RayClass.adicAbv_isNontrivial v) w hw).trans
    (localizationRamificationGroups_localDecompositionGroupEquiv
      vK (RayClass.adicAbv_isNontrivial v) w hw).symm

theorem q8QuadraticSourceChosenLocalGalEquiv_central
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceChosenLocalGalEquiv v
        (q8QuadraticSourceCentralChosenDecomposition v hv) =
      q8QuadraticSourceCentralChosenLocalEquiv v hv := by
  apply AlgEquiv.ext
  intro x
  rfl

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalLower_to_sourceLower
    (v : HeightOneSpectrum (𝓞 S))
    (n : ℕ)
    (τ : Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
      ChosenFinitePlaceBaseCompletion (K := S) v))
    (hτ : τ ∈ HilbertRamification.chosenActualLocalLowerRamificationGroup
      (K := S) (L := K3) v n) :
    let σ := (q8QuadraticSourceChosenLocalGalEquiv v).symm τ
    (σ : Gal(K3/S)) ∈
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S))
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)).asIdeal n := by
  let σ := (q8QuadraticSourceChosenLocalGalEquiv v).symm τ
  let vK := NumberField.HeightOneSpectrum.adicAbv S v
  let w := chosenFinitePlaceExtension (L := K3) v
  let hw := finitePlaceExtension_nonarchimedean (K := S) (L := K3) v w
  let eD := localizationRamificationGroups_valuationDecompositionGroupEquiv
    vK (RayClass.adicAbv_isNontrivial v) w hw
  have himage : q8QuadraticSourceChosenLocalGalEquiv v σ = τ :=
    (q8QuadraticSourceChosenLocalGalEquiv v).apply_symm_apply τ
  have hcoerce : ((eD σ :
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
        vK.Completion (algebraicLocalizationValuationSubring vK w hw)) :
      Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
        ChosenFinitePlaceBaseCompletion (K := S) v)) =
      q8QuadraticSourceChosenLocalGalEquiv v σ := by
    apply AlgEquiv.ext
    intro x
    rfl
  have hτ'eq : ((eD σ :
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
        vK.Completion (algebraicLocalizationValuationSubring vK w hw)) :
      Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
        ChosenFinitePlaceBaseCompletion (K := S) v)) = τ :=
    hcoerce.trans himage
  have hlocal : ((eD σ :
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
        vK.Completion (algebraicLocalizationValuationSubring vK w hw)) :
      Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
        ChosenFinitePlaceBaseCompletion (K := S) v)) ∈
      HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n := by
    rw [hτ'eq]
    exact hτ
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v w
  letI : IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) P.ne_bot (Localization.AtPrime P.asIdeal)
  let hDVR : IsDiscreteValuationRing (q8ChosenGlobalValuationRing v) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (q8ChosenGlobalLocalizationEquiv v).symm
  letI : IsDiscreteValuationRing
      (HilbertRamification.chosenGlobalValuationRing
        (K := S) (L := K3) v) := by
    change IsDiscreteValuationRing (q8ChosenGlobalValuationRing v)
    exact hDVR
  have hσ :=
    (HilbertRamification.chosenDecomposition_mem_chosenActualLocalLowerRamificationGroup_iff
      (K := S) (L := K3) v n σ).1 hlocal
  exact q8QuadraticSourceChosenGlobalValuationLower_le_sourceLower v n σ hσ

abbrev q8QuadraticSourceCentralChosenLocalSubgroup
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    Subgroup Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
      ChosenFinitePlaceBaseCompletion (K := S) v) :=
  Subgroup.zpowers (q8QuadraticSourceCentralChosenLocalEquiv v hv)

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalLower_le_central_of_le_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) (hn : n ≤ 2) :
    HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n ≤
      q8QuadraticSourceCentralChosenLocalSubgroup v hv := by
  intro τ hτ
  let σ := (q8QuadraticSourceChosenLocalGalEquiv v).symm τ
  have hsource := q8QuadraticSourceChosenLocalLower_to_sourceLower v n τ hτ
  have hcentral : (σ : Gal(K3/S)) ∈ q8QuadraticSourceCentralSubgroup := by
    rw [← q8QuadraticSource_lowerRamificationGroup_eq_central_of_le_two
      (finitePlaceExtensionCentre (K := S) (L := K3) v
        (chosenFinitePlaceExtension (L := K3) v)).asIdeal
      (q8FinitePlaceExtensionCentre_two_mem v hv) n hn]
    exact hsource
  rcases Subgroup.mem_zpowers_iff.mp hcentral with ⟨k, hk⟩
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  rw [← q8QuadraticSourceChosenLocalGalEquiv_central v hv, ← map_zpow]
  have hσ :
      (q8QuadraticSourceCentralChosenDecomposition v hv) ^ k = σ := by
    apply Subtype.ext
    exact hk
  rw [hσ]
  exact (q8QuadraticSourceChosenLocalGalEquiv v).apply_symm_apply τ

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceCentralChosenLocalSubgroup_le_localLower_of_le_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) (hn : n ≤ 2) :
    q8QuadraticSourceCentralChosenLocalSubgroup v hv ≤
      HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n := by
  rw [Subgroup.zpowers_le]
  let w := chosenFinitePlaceExtension (L := K3) v
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v w
  letI : IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) P.ne_bot (Localization.AtPrime P.asIdeal)
  let hDVR : IsDiscreteValuationRing (q8ChosenGlobalValuationRing v) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (q8ChosenGlobalLocalizationEquiv v).symm
  letI : IsDiscreteValuationRing
      (HilbertRamification.chosenGlobalValuationRing
        (K := S) (L := K3) v) := by
    change IsDiscreteValuationRing (q8ChosenGlobalValuationRing v)
    exact hDVR
  have hlocal :=
    (HilbertRamification.chosenDecomposition_mem_chosenActualLocalLowerRamificationGroup_iff
      (K := S) (L := K3) v n
        (q8QuadraticSourceCentralChosenDecomposition v hv)).2 (by
      intro x
      exact Ideal.pow_le_pow_right (by omega)
        (q8QuadraticSourceCentralChosenDecomposition_displacement_mem_cube v hv x))
  simpa [q8QuadraticSourceCentralChosenLocalEquiv] using hlocal

theorem q8QuadraticSourceChosenActualLocalLower_eq_central_of_le_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) (hn : n ≤ 2) :
    HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n =
      q8QuadraticSourceCentralChosenLocalSubgroup v hv := by
  apply le_antisymm
  · exact q8QuadraticSourceChosenLocalLower_le_central_of_le_two v hv n hn
  · exact q8QuadraticSourceCentralChosenLocalSubgroup_le_localLower_of_le_two v hv n hn

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenActualLocalLower_eq_bot_of_three_le
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) (hn : 3 ≤ n) :
    HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n = ⊥ := by
  apply le_antisymm
  · intro τ hτ
    rw [Subgroup.mem_bot]
    let σ := (q8QuadraticSourceChosenLocalGalEquiv v).symm τ
    have hsource := q8QuadraticSourceChosenLocalLower_to_sourceLower v n τ hτ
    have hbot : (σ : Gal(K3/S)) ∈ (⊥ : Subgroup Gal(K3/S)) := by
      rw [← q8QuadraticSource_lowerRamificationGroup_eq_bot_of_three_le
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)).asIdeal
        (q8FinitePlaceExtensionCentre_two_mem v hv) n hn]
      exact hsource
    have hσ : σ = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp hbot
    calc
      τ = q8QuadraticSourceChosenLocalGalEquiv v σ :=
        ((q8QuadraticSourceChosenLocalGalEquiv v).apply_symm_apply τ).symm
      _ = q8QuadraticSourceChosenLocalGalEquiv v 1 := congrArg _ hσ
      _ = 1 := map_one _
  · exact bot_le

theorem q8QuadraticSourceChosenActualLocalLower_profile
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) :
    HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n =
      if n ≤ 2 then q8QuadraticSourceCentralChosenLocalSubgroup v hv else ⊥ := by
  by_cases hn : n ≤ 2
  · rw [if_pos hn]
    exact q8QuadraticSourceChosenActualLocalLower_eq_central_of_le_two v hv n hn
  · rw [if_neg hn]
    exact q8QuadraticSourceChosenActualLocalLower_eq_bot_of_three_le v hv n (by omega)

end

end RHTower
