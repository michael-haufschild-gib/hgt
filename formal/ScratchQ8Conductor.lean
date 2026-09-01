import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceCompletedProfile
import LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian

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
theorem scratch_localCentral_orderOf
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

theorem scratch_localCentralSubgroup_natCard
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    Nat.card (q8QuadraticSourceCentralChosenLocalSubgroup v hv) = 2 := by
  rw [Nat.card_zpowers, scratch_localCentral_orderOf v hv]

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1200000 in
theorem scratch_chosenActualLocalLower_natCard
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) :
    Nat.card (HilbertRamification.chosenActualLocalLowerRamificationGroup
      (K := S) (L := K3) v n) = if n ≤ 2 then 2 else 1 := by
  rw [q8QuadraticSourceChosenActualLocalLower_profile v hv n]
  split_ifs with hn
  · exact scratch_localCentralSubgroup_natCard v hv
  · simp

theorem scratch_localLower_natCard
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (n : ℕ) :
    Nat.card (RamificationTheory.LocalField.localLowerRamificationGroup
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (n : ℝ)) =
      if n ≤ 2 then 2 else 1 := by
  rw [← HilbertRamification.chosenActualLocalLowerRamificationGroup_eq_localLower
    (K := S) (L := K3) v n]
  exact scratch_chosenActualLocalLower_natCard v hv n

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem scratch_localHerbrandFunction_two
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
  calc
    F.herbrandFunction (2 : ℝ) = F.herbrandValueNat 2 :=
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat F 2
    _ = 2 := by
      norm_num [F,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope,
        RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension,
        RamificationTheory.LocalField.localLowerRamificationGroup,
        scratch_localLower_natCard v hv]

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
theorem scratch_localHerbrandFunction_three
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
  calc
    F.herbrandFunction (3 : ℝ) = F.herbrandValueNat 3 :=
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat F 3
    _ = 5 / 2 := by
      norm_num [F,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope,
        RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension,
        RamificationTheory.LocalField.localLowerRamificationGroup,
        scratch_localLower_natCard v hv]

end

end RHTower
