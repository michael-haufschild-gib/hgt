import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceCompletedProfile
import LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian

/-!
# Actual local conductor of the Q8 quadratic source

The transported completed lower profile gives Herbrand values `φ(2)=2`, `φ(3)=5/2`, hence upper
groups `G^2=C₂` and `G^3=1`.  Filtered local reciprocity then proves exact local conductor exponent
three for the genuine chosen dyadic extension.
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

noncomputable local instance : IsCyclic deningerQ8ActualCyclicSubgroup := by
  have hq8 : IsCyclic q8CyclicSubgroup :=
    (MulEquiv.isCyclic q8CyclicSourceEquiv).mp inferInstance
  exact (MulEquiv.isCyclic deningerQ8ActualCyclicSubgroupEquiv).mpr hq8

noncomputable local instance : IsCyclic Gal(K3/S) :=
  (MulEquiv.isCyclic q8QuadraticSourceGalEquivCyclicSubgroup).mpr
    (inferInstance : IsCyclic deningerQ8ActualCyclicSubgroup)

noncomputable local instance q8ChosenLocalGalIsCyclic
    (v : HeightOneSpectrum (𝓞 S)) :
    IsCyclic Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
      ChosenFinitePlaceBaseCompletion (K := S) v) :=
  (MulEquiv.isCyclic (q8QuadraticSourceChosenLocalGalEquiv v)).mp inferInstance

noncomputable local instance q8ChosenLocalIsAbelianGalois
    (v : HeightOneSpectrum (𝓞 S)) :
    IsAbelianGalois
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) :=
  IsAbelianGalois.of_isCyclic _ _

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceCentralChosenLocalEquiv_orderOf
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    orderOf (q8QuadraticSourceCentralChosenLocalEquiv v hv) = 2 := by
  apply orderOf_eq_prime
  · rw [← q8QuadraticSourceChosenLocalGalEquiv_central v hv, ← map_pow]
    have hc : q8QuadraticSourceCentral ^ 2 = 1 := by
      rw [← q8QuadraticSourceCentral_orderOf]
      exact pow_orderOf_eq_one q8QuadraticSourceCentral
    have hD : (q8QuadraticSourceCentralChosenDecomposition v hv) ^ 2 = 1 := by
      apply Subtype.ext
      exact hc
    rw [hD, map_one]
  · intro hone
    apply q8QuadraticSourceCentralChosenLocalEquiv_not_mem_actualLower_three v hv
    rw [hone]
    exact Subgroup.one_mem _

theorem q8QuadraticSourceCentralChosenLocalSubgroup_natCard
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    Nat.card (q8QuadraticSourceCentralChosenLocalSubgroup v hv) = 2 := by
  rw [Nat.card_zpowers, q8QuadraticSourceCentralChosenLocalEquiv_orderOf v hv]

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1200000 in
theorem q8QuadraticSourceChosenActualLocalLower_natCard
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) :
    Nat.card (HilbertRamification.chosenActualLocalLowerRamificationGroup
      (K := S) (L := K3) v n) = if n ≤ 2 then 2 else 1 := by
  rw [q8QuadraticSourceChosenActualLocalLower_profile v hv n]
  split_ifs with hn
  · exact q8QuadraticSourceCentralChosenLocalSubgroup_natCard v hv
  · simp

theorem q8QuadraticSourceChosenLocalLower_natCard
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) :
    Nat.card (RamificationTheory.LocalField.localLowerRamificationGroup
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (n : ℝ)) =
      if n ≤ 2 then 2 else 1 := by
  rw [← HilbertRamification.chosenActualLocalLowerRamificationGroup_eq_localLower
    (K := S) (L := K3) v n]
  exact q8QuadraticSourceChosenActualLocalLower_natCard v hv n

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalHerbrandFunction_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let B := ChosenFinitePlaceBaseCompletion (K := S) v
    let E := ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v
    RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension
      (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
      (2 : ℝ) = 2 := by
  dsimp only
  let F :=
    RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension
      (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension
        (ChosenFinitePlaceBaseCompletion (K := S) v)
        (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v))
  change F.herbrandFunction (2 : ℝ) = 2
  have hcard (n : ℕ) : Nat.card (F.lower n) = if n ≤ 2 then 2 else 1 := by
    change Nat.card (RamificationTheory.LocalField.localLowerRamificationGroup
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (n : ℝ)) = _
    exact q8QuadraticSourceChosenLocalLower_natCard v hv n
  calc
    F.herbrandFunction (2 : ℝ) = F.herbrandValueNat 2 :=
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat F 2
    _ = 2 := by
      norm_num [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope,
        hcard, Finset.sum_range_succ]

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalHerbrandFunction_three
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let B := ChosenFinitePlaceBaseCompletion (K := S) v
    let E := ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v
    RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension
      (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
      (3 : ℝ) = 5 / 2 := by
  dsimp only
  let F :=
    RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension
      (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension
        (ChosenFinitePlaceBaseCompletion (K := S) v)
        (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v))
  change F.herbrandFunction (3 : ℝ) = 5 / 2
  have hcard (n : ℕ) : Nat.card (F.lower n) = if n ≤ 2 then 2 else 1 := by
    change Nat.card (RamificationTheory.LocalField.localLowerRamificationGroup
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (n : ℝ)) = _
    exact q8QuadraticSourceChosenLocalLower_natCard v hv n
  calc
    F.herbrandFunction (3 : ℝ) = F.herbrandValueNat 3 :=
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat F 3
    _ = 5 / 2 := by
      norm_num [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope,
        hcard, Finset.sum_range_succ]

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalUpper_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    RamificationTheory.LocalField.localUpperRamificationGroup
        (ChosenFinitePlaceBaseCompletion (K := S) v)
        (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (2 : ℝ) =
      q8QuadraticSourceCentralChosenLocalSubgroup v hv := by
  let B := ChosenFinitePlaceBaseCompletion (K := S) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v
  have hu :=
    RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension_herbrandFunction
      (base := (LocalFieldTheory.localCompleteDVF B).toDVF)
      (target := (LocalFieldTheory.chosenLocalExtensionCompleteDVF B E).toDVF)
      (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
      (2 : ℝ)
  have hphi := q8QuadraticSourceChosenLocalHerbrandFunction_two v hv
  have hu2 :
      RamificationTheory.LocalField.localUpperRamificationGroup B E (2 : ℝ) =
        RamificationTheory.LocalField.localLowerRamificationGroup B E (2 : ℝ) := by
    change RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension
      (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
      (2 : ℝ) =
        RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup
          (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
          (2 : ℝ)
    calc
      RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension
          (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
          (2 : ℝ) =
        RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension
          (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
          (RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension
            (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
            (2 : ℝ)) := congrArg _ hphi.symm
      _ = _ := hu
  rw [hu2]
  dsimp only [B, E]
  exact
    (HilbertRamification.chosenActualLocalLowerRamificationGroup_eq_localLower
      (K := S) (L := K3) v 2).symm.trans
      (q8QuadraticSourceChosenActualLocalLower_eq_central_of_le_two v hv 2 (by omega))

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalUpper_three
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    RamificationTheory.LocalField.localUpperRamificationGroup
        (ChosenFinitePlaceBaseCompletion (K := S) v)
        (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (3 : ℝ) = ⊥ := by
  let B := ChosenFinitePlaceBaseCompletion (K := S) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v
  have hu :=
    RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension_herbrandFunction
      (base := (LocalFieldTheory.localCompleteDVF B).toDVF)
      (target := (LocalFieldTheory.chosenLocalExtensionCompleteDVF B E).toDVF)
      (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
      (3 : ℝ)
  have hphi := q8QuadraticSourceChosenLocalHerbrandFunction_three v hv
  have huAt :
      RamificationTheory.LocalField.localUpperRamificationGroup B E (5 / 2 : ℝ) =
        RamificationTheory.LocalField.localLowerRamificationGroup B E (3 : ℝ) := by
    change RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension
      (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
      (5 / 2 : ℝ) =
        RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup
          (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
          (3 : ℝ)
    calc
      RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension
          (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
          (5 / 2 : ℝ) =
        RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension
          (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
          (RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension
            (LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E)
            (3 : ℝ)) := congrArg _ hphi.symm
      _ = _ := hu
  have hLowerThree :
      RamificationTheory.LocalField.localLowerRamificationGroup B E (3 : ℝ) = ⊥ := by
    dsimp only [B, E]
    exact
      (HilbertRamification.chosenActualLocalLowerRamificationGroup_eq_localLower
        (K := S) (L := K3) v 3).symm.trans
        (q8QuadraticSourceChosenActualLocalLower_eq_bot_of_three_le v hv 3 (by omega))
  have hAtBot :
      RamificationTheory.LocalField.localUpperRamificationGroup B E (5 / 2 : ℝ) = ⊥ := by
    rw [huAt, hLowerThree]
  apply le_antisymm
  · have hle := RamificationTheory.LocalField.localUpperRamificationGroup_antitone
      B E (show (5 / 2 : ℝ) ≤ 3 by norm_num)
    rw [hAtBot] at hle
    exact hle
  · exact bot_le

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1200000 in
theorem q8QuadraticSourceCentralChosenLocalSubgroup_ne_bot
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceCentralChosenLocalSubgroup v hv ≠ ⊥ := by
  intro hbot
  have hmem : q8QuadraticSourceCentralChosenLocalEquiv v hv ∈
      q8QuadraticSourceCentralChosenLocalSubgroup v hv :=
    Subgroup.mem_zpowers _
  rw [hbot, Subgroup.mem_bot] at hmem
  have hne : q8QuadraticSourceCentralChosenLocalEquiv v hv ≠ 1 := by
    intro hone
    have hord := q8QuadraticSourceCentralChosenLocalEquiv_orderOf v hv
    rw [hone, orderOf_one] at hord
    norm_num at hord
  exact hne hmem

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalArtinPrincipalUnit_two_ne_bot
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    LocalClassFieldTheory.artinPrincipalUnitGroup
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) 2 ≠ ⊥ := by
  have hfiltered := LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity
    (ChosenFinitePlaceBaseCompletion (K := S) v)
    (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v)
    (2 : ℝ) (by norm_num)
  have hstep : LocalClassFieldTheory.artinPrincipalUnitStepGroup
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (2 : ℝ) =
      q8QuadraticSourceCentralChosenLocalSubgroup v hv :=
    hfiltered.trans (q8QuadraticSourceChosenLocalUpper_two v hv)
  have hne := q8QuadraticSourceCentralChosenLocalSubgroup_ne_bot v hv
  simpa [LocalClassFieldTheory.artinPrincipalUnitStepGroup,
    RamificationTheory.natCeilStepFiltration] using
      (show LocalClassFieldTheory.artinPrincipalUnitStepGroup
        (ChosenFinitePlaceBaseCompletion (K := S) v)
        (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v)
        (2 : ℝ) ≠ ⊥ by
        rw [hstep]
        exact hne)

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalArtinPrincipalUnit_three_eq_bot
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    LocalClassFieldTheory.artinPrincipalUnitGroup
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) 3 = ⊥ := by
  have hfiltered := LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity
    (ChosenFinitePlaceBaseCompletion (K := S) v)
    (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v)
    (3 : ℝ) (by norm_num)
  have hstep : LocalClassFieldTheory.artinPrincipalUnitStepGroup
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v)
      (3 : ℝ) = ⊥ :=
    hfiltered.trans (q8QuadraticSourceChosenLocalUpper_three v hv)
  simpa [LocalClassFieldTheory.artinPrincipalUnitStepGroup,
    RamificationTheory.natCeilStepFiltration] using hstep

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem q8QuadraticSourceChosenLocalConductorExponent_eq_three
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    LocalClassFieldTheory.localConductorExponent
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) = 3 := by
  have htwo : 2 < LocalClassFieldTheory.localConductorExponent
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) :=
    (LocalClassFieldTheory.artinPrincipalUnitGroup_ne_bot_iff
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) 2).1
      (q8QuadraticSourceChosenLocalArtinPrincipalUnit_two_ne_bot v hv)
  have hthree : LocalClassFieldTheory.localConductorExponent
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) ≤ 3 :=
    (LocalClassFieldTheory.artinPrincipalUnitGroup_eq_bot_iff
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) 3).1
      (q8QuadraticSourceChosenLocalArtinPrincipalUnit_three_eq_bot v hv)
  omega

end

end RHTower
