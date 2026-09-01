import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceHigherRamification

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

local instance : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance : FiniteDimensional S K2 := by infer_instance
noncomputable local instance : FiniteDimensional S K3 :=
  FiniteDimensional.trans S K2 K3
noncomputable local instance : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance : NumberField S := NumberField.mk
noncomputable local instance : NumberField K2 := NumberField.mk
noncomputable local instance : NumberField K3 := NumberField.mk
noncomputable local instance : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
noncomputable local instance : IsGalois S K3 :=
  IsGalois.tower_top_of_isGalois ℚ S K3

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem scratch_globalValuationLower_le_sourceLower
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

noncomputable def scratch_q8ChosenLocalGalEquiv
    (v : HeightOneSpectrum (𝓞 S)) :
    RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup S
        (q8ChosenGlobalValuationRing v) ≃*
      Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
        ChosenFinitePlaceBaseCompletion (K := S) v) :=
  let vK := HeightOneSpectrum.adicAbv S v
  let w := chosenFinitePlaceExtension (L := K3) v
  let hw := finitePlaceExtension_nonarchimedean (K := S) (L := K3) v w
  (localizationRamificationGroups_valuationDecompositionGroupEquiv
      vK (RayClass.adicAbv_isNontrivial v) w hw).trans
    (localizationRamificationGroups_localDecompositionGroupEquiv
      vK (RayClass.adicAbv_isNontrivial v) w hw).symm

theorem scratch_q8ChosenLocalGalEquiv_central
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    scratch_q8ChosenLocalGalEquiv v
        (q8QuadraticSourceCentralChosenDecomposition v hv) =
      q8QuadraticSourceCentralChosenLocalEquiv v hv := by
  apply AlgEquiv.ext
  intro x
  rfl

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem scratch_localLower_to_sourceLower
    (v : HeightOneSpectrum (𝓞 S))
    (n : ℕ)
    (τ : Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
      ChosenFinitePlaceBaseCompletion (K := S) v))
    (hτ : τ ∈ HilbertRamification.chosenActualLocalLowerRamificationGroup
      (K := S) (L := K3) v n) :
    let σ := (scratch_q8ChosenLocalGalEquiv v).symm τ
    (σ : Gal(K3/S)) ∈
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S))
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)).asIdeal n := by
  let σ := (scratch_q8ChosenLocalGalEquiv v).symm τ
  have himage : scratch_q8ChosenLocalGalEquiv v σ = τ :=
    (scratch_q8ChosenLocalGalEquiv v).apply_symm_apply τ
  have hlocal :
      let vK := HeightOneSpectrum.adicAbv S v
      let w := chosenFinitePlaceExtension (L := K3) v
      let τD := localizationRamificationGroups_valuationDecompositionGroupEquiv
        vK (RayClass.adicAbv_isNontrivial v) w
          (finitePlaceExtension_nonarchimedean (K := S) (L := K3) v w) σ
      let τ' : ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v ≃ₐ[
        ChosenFinitePlaceBaseCompletion (K := S) v]
          ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v := τD
      τ' ∈ HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n := by
    simpa [scratch_q8ChosenLocalGalEquiv, σ] using hτ
  have hσ :=
    (HilbertRamification.chosenDecomposition_mem_chosenActualLocalLowerRamificationGroup_iff
      (K := S) (L := K3) v n σ).1 hlocal
  exact scratch_globalValuationLower_le_sourceLower v n σ hσ

abbrev scratch_q8CentralChosenLocalSubgroup
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    Subgroup Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
      ChosenFinitePlaceBaseCompletion (K := S) v) :=
  Subgroup.zpowers (q8QuadraticSourceCentralChosenLocalEquiv v hv)

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem scratch_localLower_le_central_of_le_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) (hn : n ≤ 2) :
    HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n ≤
      scratch_q8CentralChosenLocalSubgroup v hv := by
  intro τ hτ
  let σ := (scratch_q8ChosenLocalGalEquiv v).symm τ
  have hsource := scratch_localLower_to_sourceLower v n τ hτ
  have hcentral : (σ : Gal(K3/S)) ∈ q8QuadraticSourceCentralSubgroup := by
    rw [← q8QuadraticSource_lowerRamificationGroup_eq_central_of_le_two
      (finitePlaceExtensionCentre (K := S) (L := K3) v
        (chosenFinitePlaceExtension (L := K3) v)).asIdeal
      (q8FinitePlaceExtensionCentre_two_mem v hv) n hn]
    exact hsource
  rcases Subgroup.mem_zpowers_iff.mp hcentral with ⟨k, hk⟩
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  rw [← scratch_q8ChosenLocalGalEquiv_central v hv, ← map_zpow]
  have hσ :
      (q8QuadraticSourceCentralChosenDecomposition v hv) ^ k = σ := by
    apply Subtype.ext
    exact hk
  rw [hσ]
  exact (scratch_q8ChosenLocalGalEquiv v).apply_symm_apply τ

set_option maxHeartbeats 1200000 in
theorem scratch_central_le_localLower_of_le_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) (hn : n ≤ 2) :
    scratch_q8CentralChosenLocalSubgroup v hv ≤
      HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n := by
  rw [Subgroup.zpowers_le]
  apply (HilbertRamification.mem_chosenActualLocalLowerRamificationGroup_iff
    (K := S) (L := K3) v n _).2
  intro z
  have hcube := q8QuadraticSourceCentralChosenCompletion_displacement_mem_cube
    v hv z
  exact Ideal.pow_le_pow_right (by omega) hcube

theorem scratch_localLower_eq_central_of_le_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) (hn : n ≤ 2) :
    HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n =
      scratch_q8CentralChosenLocalSubgroup v hv := by
  apply le_antisymm
  · exact scratch_localLower_le_central_of_le_two v hv n hn
  · exact scratch_central_le_localLower_of_le_two v hv n hn

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem scratch_localLower_eq_bot_of_three_le
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) (hn : 3 ≤ n) :
    HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n = ⊥ := by
  apply le_antisymm
  · intro τ hτ
    rw [Subgroup.mem_bot]
    let σ := (scratch_q8ChosenLocalGalEquiv v).symm τ
    have hsource := scratch_localLower_to_sourceLower v n τ hτ
    have hbot : (σ : Gal(K3/S)) ∈ (⊥ : Subgroup Gal(K3/S)) := by
      rw [← q8QuadraticSource_lowerRamificationGroup_eq_bot_of_three_le
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)).asIdeal
        (q8FinitePlaceExtensionCentre_two_mem v hv) n hn]
      exact hsource
    have hσ : σ = 1 := Subgroup.mem_bot.mp hbot
    have hτ := (scratch_q8ChosenLocalGalEquiv v).apply_symm_apply τ
    rw [hσ, map_one] at hτ
    exact hτ.symm
  · exact bot_le

theorem scratch_localLower_profile
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) :
    HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v n =
      if n ≤ 2 then scratch_q8CentralChosenLocalSubgroup v hv else ⊥ := by
  by_cases hn : n ≤ 2
  · rw [if_pos hn]
    exact scratch_localLower_eq_central_of_le_two v hv n hn
  · rw [if_neg hn]
    exact scratch_localLower_eq_bot_of_three_le v hv n (by omega)

end

end RHTower
