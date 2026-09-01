import AlgebraicNumberTheory.Completion.ChosenLocalization
import AlgebraicNumberTheory.Completion.ExtensionIndex
import RamificationTheory.HilbertRamification.LocalizationRamificationGroups
import LocalFieldTheory.NonarchimedeanLocalField.PrincipalUnitQuotients
import GaloisForLFunctions.HTGeometry.KaehlerRamificationCriterion
import GaloisForLFunctions.HTGeometry.LocalRamificationOrderLaw
import GaloisForLFunctions.HTGeometry.LowerRamificationGroup
import RamificationTheory.LocalField.Core
import LocalFieldTheory.NonarchimedeanLocalField.NormalizedIntegerValuation

noncomputable section

open scoped NumberField Classical ValuativeRel NNReal
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open LocalFieldTheory

namespace HilbertRamification

variable {K L : Type}
  [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

abbrev chosenGlobalValuationRing (v₀ : HeightOneSpectrum (𝓞 K)) :=
  absoluteValueValuationSubring
    (chosenFinitePlaceExtension (L := L) v₀).1
    (finitePlaceExtension_nonarchimedean
      (K := K) (L := L) v₀ (chosenFinitePlaceExtension (L := L) v₀))

abbrev chosenLocalIntegerRing (v₀ : HeightOneSpectrum (𝓞 K)) :=
  𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]

noncomputable instance chosenLocalIntegerRingIsLocal
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    IsLocalRing (chosenLocalIntegerRing (K := K) (L := L) v₀) :=
  ValuationSubring.isLocalRing
    ((ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)).valuationSubring)

/-- Identity-on-the-field equivalence between the canonical complete-DVF valuation subring and
the intrinsic local integer ring. -/
noncomputable def chosenActualValuationSubringEquivIntegerRing
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    (LocalFieldTheory.localCompleteDVF
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)).valuation.valuationSubring ≃+*
      chosenLocalIntegerRing (K := K) (L := L) v₀ where
  toFun x := ⟨x, by
    change ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀) (x : _) ≤ 1
    rw [← LocalFieldTheory.localCompleteDVF_valuation_eq]
    exact x.property⟩
  invFun x := ⟨x, by
    change (LocalFieldTheory.localCompleteDVF
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)).valuation (x : _) ≤ 1
    rw [LocalFieldTheory.localCompleteDVF_valuation_eq]
    exact x.property⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

noncomputable def chosenGlobalToLocalIntegerRing
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    chosenGlobalValuationRing (K := K) (L := L) v₀ →+*
      chosenLocalIntegerRing (K := K) (L := L) v₀ where
  toFun x := ⟨AbsoluteValue.toAlgebraicLocalization
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2 (x : L), by
    apply (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).2
    change (AbsoluteValue.algebraicLocalizationAbsoluteValue
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2)
        (AbsoluteValue.toAlgebraicLocalization
          (HeightOneSpectrum.adicAbv K v₀)
          (chosenFinitePlaceExtension (L := L) v₀).1
          (chosenFinitePlaceExtension (L := L) v₀).2 (x : L)) ≤ 1
    rw [AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization]
    exact (mem_absoluteValueValuationSubring_iff _ _ _).mp x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem chosenGlobalToLocalIntegerRing_mem_maximalIdeal_pow
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {x : chosenGlobalValuationRing (K := K) (L := L) v₀}
    (hx : x ∈ IsLocalRing.maximalIdeal
      (chosenGlobalValuationRing (K := K) (L := L) v₀) ^ n) :
    chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x ∈
      IsLocalRing.maximalIdeal
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n := by
  let f := chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀
  have hmap : Ideal.map f
      (IsLocalRing.maximalIdeal
        (chosenGlobalValuationRing (K := K) (L := L) v₀)) ≤
      IsLocalRing.maximalIdeal
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change f y ∈ IsLocalRing.maximalIdeal
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hyAbs : (chosenFinitePlaceExtension (L := L) v₀).1 (y : L) < 1 :=
      (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one _ _ y).mp hy
    have hyNorm : ‖(f y :
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀])‖ < 1 := by
      change (AbsoluteValue.algebraicLocalizationAbsoluteValue
        (HeightOneSpectrum.adicAbv K v₀)
        (chosenFinitePlaceExtension (L := L) v₀).1
        (chosenFinitePlaceExtension (L := L) v₀).2)
          (AbsoluteValue.toAlgebraicLocalization
            (HeightOneSpectrum.adicAbv K v₀)
            (chosenFinitePlaceExtension (L := L) v₀).1
            (chosenFinitePlaceExtension (L := L) v₀).2 (y : L)) < 1
      rw [AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization]
      exact hyAbs
    apply (Valuation.Integer.not_isUnit_iff_valuation_lt_one).2
    let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
    let zE : E := (f y : 𝒪[E])
    rw [lt_iff_not_ge]
    intro hge
    have hgeRel : (1 : E) ≤ᵥ zE :=
      (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation E) (1 : E) zE).2 hge
    have hgeVal : (1 : ℝ≥0) ≤ (Valued.v : Valuation E ℝ≥0) zE :=
      by simpa using
        (Valuation.Compatible.vle_iff_le
          (v := (Valued.v : Valuation E ℝ≥0)) (1 : E) zE).1 hgeRel
    have hgeNorm : (1 : ℝ) ≤ ‖zE‖ := by exact_mod_cast hgeVal
    exact (not_le_of_gt hyNorm) hgeNorm
  have hxmap := Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow] at hxmap
  exact (pow_le_pow_left' hmap n) hxmap

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1200000 in
/-- The canonical dense embedding reflects the maximal ideal itself.  This is the exact
level-one input used below to prove that a source uniformizer remains a uniformizer after
completion. -/
theorem chosenGlobalToLocalIntegerRing_mem_maximalIdeal_iff
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x : chosenGlobalValuationRing (K := K) (L := L) v₀) :
    chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x ∈
        IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ↔
      x ∈ IsLocalRing.maximalIdeal
        (chosenGlobalValuationRing (K := K) (L := L) v₀) := by
  let f := chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
  constructor
  · intro hx
    have hxNonunit : ¬ IsUnit (f x) := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    have hxVal : (ValuativeRel.valuation E) ((f x : 𝒪[E]) : E) < 1 :=
      (Valuation.Integer.not_isUnit_iff_valuation_lt_one).1 hxNonunit
    have hxNorm : ‖((f x : 𝒪[E]) : E)‖ < 1 := by
      rw [lt_iff_not_ge]
      intro hgeNorm
      have hgeValNN : (1 : ℝ≥0) ≤
          (Valued.v : Valuation E ℝ≥0) ((f x : 𝒪[E]) : E) := by
        exact_mod_cast hgeNorm
      have hgeRel : (1 : E) ≤ᵥ ((f x : 𝒪[E]) : E) :=
        (Valuation.Compatible.vle_iff_le
          (v := (Valued.v : Valuation E ℝ≥0)) (1 : E) ((f x : 𝒪[E]) : E)).2
            (by simpa using hgeValNN)
      have hgeVal : (1 : ValuativeRel.ValueGroupWithZero E) ≤
          (ValuativeRel.valuation E) ((f x : 𝒪[E]) : E) :=
        (Valuation.Compatible.vle_iff_le
          (v := ValuativeRel.valuation E) (1 : E) ((f x : 𝒪[E]) : E)).1 hgeRel
      exact (not_le_of_gt hxVal) hgeVal
    apply (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
      (chosenFinitePlaceExtension (L := L) v₀).1
      (finitePlaceExtension_nonarchimedean
        (K := K) (L := L) v₀ (chosenFinitePlaceExtension (L := L) v₀)) x).2
    change (AbsoluteValue.algebraicLocalizationAbsoluteValue
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2)
        (AbsoluteValue.toAlgebraicLocalization
          (HeightOneSpectrum.adicAbv K v₀)
          (chosenFinitePlaceExtension (L := L) v₀).1
          (chosenFinitePlaceExtension (L := L) v₀).2 (x : L)) < 1 at hxNorm
    rw [AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization] at hxNorm
    exact hxNorm
  · intro hx
    have hxAbs : (chosenFinitePlaceExtension (L := L) v₀).1 (x : L) < 1 :=
      (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
        (chosenFinitePlaceExtension (L := L) v₀).1
        (finitePlaceExtension_nonarchimedean
          (K := K) (L := L) v₀ (chosenFinitePlaceExtension (L := L) v₀)) x).1 hx
    have hxNorm : ‖((f x : 𝒪[E]) : E)‖ < 1 := by
      change (AbsoluteValue.algebraicLocalizationAbsoluteValue
        (HeightOneSpectrum.adicAbv K v₀)
        (chosenFinitePlaceExtension (L := L) v₀).1
        (chosenFinitePlaceExtension (L := L) v₀).2)
          (AbsoluteValue.toAlgebraicLocalization
            (HeightOneSpectrum.adicAbv K v₀)
            (chosenFinitePlaceExtension (L := L) v₀).1
            (chosenFinitePlaceExtension (L := L) v₀).2 (x : L)) < 1
      rw [AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization]
      exact hxAbs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    apply (Valuation.Integer.not_isUnit_iff_valuation_lt_one).2
    rw [lt_iff_not_ge]
    intro hge
    have hgeRel : (1 : E) ≤ᵥ ((f x : 𝒪[E]) : E) :=
      (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation E) (1 : E) ((f x : 𝒪[E]) : E)).2 hge
    have hgeVal : (Valued.v : Valuation E ℝ≥0) (1 : E) ≤
        (Valued.v : Valuation E ℝ≥0) ((f x : 𝒪[E]) : E) :=
      (Valuation.Compatible.vle_iff_le
        (v := (Valued.v : Valuation E ℝ≥0)) (1 : E) ((f x : 𝒪[E]) : E)).1 hgeRel
    have hgeNorm : (1 : ℝ) ≤ ‖((f x : 𝒪[E]) : E)‖ := by
      have hgeVal' : (1 : ℝ≥0) ≤
          (Valued.v : Valuation E ℝ≥0) ((f x : 𝒪[E]) : E) := by
        simpa using hgeVal
      exact_mod_cast hgeVal'
    exact (not_le_of_gt hxNorm) hgeNorm

noncomputable def chosenLocalIntegerRingAut
    (v₀ : HeightOneSpectrum (𝓞 K))
    (τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀) :
    𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ≃+*
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] where
  toFun x := ⟨τ (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀), by
    apply (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).2
    have hx := (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).1 x.property
    change (AbsoluteValue.algebraicLocalizationAbsoluteValue
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2) (τ (x : _)) ≤ 1
    rw [algebraicLocalizationDensity_localizationAbsoluteValue_algEquiv
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (RayClass.adicAbv_isNontrivial v₀) τ]
    exact hx⟩
  invFun x := ⟨τ.symm (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀), by
    apply (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).2
    have hx := (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).1 x.property
    change (AbsoluteValue.algebraicLocalizationAbsoluteValue
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2) (τ.symm (x : _)) ≤ 1
    rw [algebraicLocalizationDensity_localizationAbsoluteValue_algEquiv
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (RayClass.adicAbv_isNontrivial v₀) τ.symm]
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    exact τ.symm_apply_apply (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
  right_inv x := by
    apply Subtype.ext
    exact τ.apply_symm_apply (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul τ
      (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
      (y : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
  map_add' x y := by
    apply Subtype.ext
    exact map_add τ
      (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
      (y : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)

theorem chosenLocalIntegerRingAut_mem_maximalIdeal_pow_iff
    (v₀ : HeightOneSpectrum (𝓞 K))
    (τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
    (n : ℕ) (x : 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]) :
    chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ x ∈
        IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n ↔
      x ∈ IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n :=
  ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
    (chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ) n x

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1200000 in
/-- Lower ramification formed with the completion's actual canonical valuation.  Keeping this
subgroup named prevents later proofs from unfolding CFT's arbitrary chosen integral-closure
valuation. -/
noncomputable def chosenActualLocalLowerRamificationGroup
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀) := by
  let B := ChosenFinitePlaceBaseCompletion (K := K) v₀
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
  let base := LocalFieldTheory.localCompleteDVF B
  let actual := LocalFieldTheory.localCompleteDVF E
  letI : base.valuation.HasExtension actual.valuation :=
    LocalFieldTheory.localCompleteDVFValuation_hasExtension B E
  let huniqActual :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF actual.toDVF :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.hasUniqueValuationExtension_of_finite_separable
      base actual
  exact RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup
    (base := base.toDVF) (target := actual.toDVF) huniqActual (n : ℝ)

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
/-- CFT's chosen integral-closure valuation and the completion's actual valuation give the same
local lower filtration. -/
theorem chosenActualLocalLowerRamificationGroup_eq_localLower
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    chosenActualLocalLowerRamificationGroup (K := K) (L := L) v₀ n =
      RamificationTheory.LocalField.localLowerRamificationGroup
        (ChosenFinitePlaceBaseCompletion (K := K) v₀)
        (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀) (n : ℝ) := by
  let B := ChosenFinitePlaceBaseCompletion (K := K) v₀
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
  let base := LocalFieldTheory.localCompleteDVF B
  let chosen := LocalFieldTheory.chosenLocalExtensionCompleteDVF B E
  let actual := LocalFieldTheory.localCompleteDVF E
  letI : base.valuation.HasExtension actual.valuation :=
    LocalFieldTheory.localCompleteDVFValuation_hasExtension B E
  let huniqChosen :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF chosen.toDVF :=
    LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension B E
  let huniqActual :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF actual.toDVF :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.hasUniqueValuationExtension_of_finite_separable
      base actual
  have hvaluationSubring :
      chosen.valuation.valuationSubring = actual.valuation.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring
      chosen.valuation actual.valuation).1 (huniqChosen actual.valuation)
  exact
    (RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_eq_of_valuationSubring_eq
      huniqChosen huniqActual hvaluationSubring (n : ℝ)).symm

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
/-- Exact completed displacement criterion for the actual local lower filtration.  The right side
uses the intrinsic local integer ring, hence can consume coefficient-faithful source-completion
identities directly. -/
theorem mem_chosenActualLocalLowerRamificationGroup_iff
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀) :
    τ ∈ chosenActualLocalLowerRamificationGroup (K := K) (L := L) v₀ n ↔
      ∀ z : chosenLocalIntegerRing (K := K) (L := L) v₀,
        chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ z - z ∈
          IsLocalRing.maximalIdeal
            (chosenLocalIntegerRing (K := K) (L := L) v₀) ^ (n + 1) := by
  let B := ChosenFinitePlaceBaseCompletion (K := K) v₀
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
  let base := LocalFieldTheory.localCompleteDVF B
  let actual := LocalFieldTheory.localCompleteDVF E
  letI : base.valuation.HasExtension actual.valuation :=
    LocalFieldTheory.localCompleteDVFValuation_hasExtension B E
  let huniqActual :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF actual.toDVF :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.hasUniqueValuationExtension_of_finite_separable
      base actual
  let e := chosenActualValuationSubringEquivIntegerRing (K := K) (L := L) v₀
  change τ ∈
      RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup
        huniqActual (n : ℝ) ↔ _
  rw [RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_nat_iff]
  constructor
  · intro h z
    let z' := e.symm z
    have hz' := h z'
    have hmap :
        e (RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension
              huniqActual τ z' - z') ∈
          IsLocalRing.maximalIdeal
            (chosenLocalIntegerRing (K := K) (L := L) v₀) ^ (n + 1) :=
      (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff e (n + 1) _).2 hz'
    have heq :
        e (RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension
              huniqActual τ z' - z') =
          chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ z - z := by
      apply Subtype.ext
      rfl
    rwa [heq] at hmap
  · intro h z
    have hz := h (e z)
    have heq :
        e (RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension
              huniqActual τ z - z) =
          chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ (e z) - e z := by
      apply Subtype.ext
      rfl
    apply (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff e (n + 1) _).1
    rwa [heq]

/-- One intrinsic-integer displacement outside `m^(n+1)` excludes an automorphism from actual
completed lower level `n`. -/
theorem not_mem_chosenActualLocalLowerRamificationGroup_of_displacement
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
    (z : chosenLocalIntegerRing (K := K) (L := L) v₀)
    (hz : chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ z - z ∉
      IsLocalRing.maximalIdeal
        (chosenLocalIntegerRing (K := K) (L := L) v₀) ^ (n + 1)) :
    τ ∉ chosenActualLocalLowerRamificationGroup (K := K) (L := L) v₀ n := by
  intro hτ
  exact hz ((mem_chosenActualLocalLowerRamificationGroup_iff
    (K := K) (L := L) v₀ n τ).1 hτ z)

theorem chosenGlobalToLocalIntegerRing_denseRange
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    DenseRange (chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀) := by
  rw [Metric.denseRange_iff]
  intro z r hr
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
  have heps : 0 < min r 1 := lt_min hr (by norm_num)
  obtain ⟨x, hx⟩ :=
    algebraicLocalizationDensity_localization_exists_close vK w
      (z : E) heps
  have hz : ‖(z : E)‖ ≤ 1 :=
    (localizedCompletion_mem_integers_iff_norm_le_one vK w
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).1 z.property
  have hstrong : ‖(z : E) + -((z : E) -
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)‖ ≤
      max ‖(z : E)‖ ‖-((z : E) -
        AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)‖ :=
    IsUltrametricDist.norm_add_le_max _ _
  have hxLocal : ‖AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ ≤ 1 := by
    calc
      ‖AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ =
          ‖(z : E) + -((z : E) -
            AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)‖ := by
        congr 1
        ring
      _ ≤ max ‖(z : E)‖ ‖-((z : E) -
          AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)‖ := hstrong
      _ = max ‖(z : E)‖ ‖(z : E) -
          AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ := by rw [norm_neg]
      _ ≤ 1 := max_le hz (hx.le.trans (min_le_right _ _))
  have hxGlobal : w.1 x ≤ 1 := by
    change ‖AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ ≤ 1 at hxLocal
    rw [← AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization
      vK w.1 w.2 x]
    exact hxLocal
  let xA : chosenGlobalValuationRing (K := K) (L := L) v₀ :=
    ⟨x, (mem_absoluteValueValuationSubring_iff _ _ _).mpr hxGlobal⟩
  refine ⟨xA, ?_⟩
  rw [dist_eq_norm]
  change ‖(z : E) - AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ < r
  exact hx.trans_le (min_le_left _ _)

set_option maxHeartbeats 800000 in
theorem chosenGlobalToLocalIntegerRing_exists_approx_mod_maximalIdeal_pow
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (z : 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]) :
    ∃ x : chosenGlobalValuationRing (K := K) (L := L) v₀,
      z - chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x ∈
        IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n := by
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
  let I := IsLocalRing.maximalIdeal
    𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n
  have hIopen : IsOpen (I : Set 𝒪[ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v₀]) :=
    I.toAddSubgroup.isOpen_of_mem_nhds (LocalFieldTheory.maximalIdeal_pow_mem_nhds_zero E n)
  let U : Set 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] :=
    {y | y - z ∈ I}
  have hUopen : IsOpen U := hIopen.preimage (continuous_id.sub continuous_const)
  have hUne : U.Nonempty := by
    refine ⟨z, ?_⟩
    change z - z ∈ I
    rw [sub_self]
    exact I.zero_mem
  obtain ⟨x, hx⟩ :=
    (chosenGlobalToLocalIntegerRing_denseRange (K := K) (L := L) v₀).exists_mem_open
      hUopen hUne
  refine ⟨x, ?_⟩
  have hx' : chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x - z ∈ I := hx
  have hneg := I.neg_mem hx'
  convert hneg using 1 <;> ring

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1200000 in
private theorem chosenLocalIntegerRing_not_maximalIdeal_le_sq
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    ¬ (IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ≤
        IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ 2) := by
  intro h
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (IsLocalRing.maximalIdeal
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀])
    (IsLocalRing.maximalIdeal
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀])
    (IsNoetherian.noetherian _) (by rwa [smul_eq_mul, ← pow_two])
    (IsLocalRing.maximalIdeal_le_jacobson _)
  exact IsDiscreteValuationRing.not_a_field
    𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] hbot

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1200000 in
/-- A source uniformizer remains a uniformizer in the completed local integer ring.  Density
modulo the square rules out collapse into the second maximal-ideal power; the DVR ideal
classification then gives irreducibility. -/
theorem chosenGlobalToLocalIntegerRing_map_irreducible
    (v₀ : HeightOneSpectrum (𝓞 K))
    [IsDiscreteValuationRing
      (chosenGlobalValuationRing (K := K) (L := L) v₀)]
    {π : chosenGlobalValuationRing (K := K) (L := L) v₀}
    (hπ : Irreducible π) :
    Irreducible
      (chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ π) := by
  let A := chosenGlobalValuationRing (K := K) (L := L) v₀
  let B := 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]
  let f : A →+* B := chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀
  let mB := IsLocalRing.maximalIdeal B
  have hfm : f π ∈ mB :=
    (chosenGlobalToLocalIntegerRing_mem_maximalIdeal_iff
      (K := K) (L := L) v₀ π).2
      (by rw [hπ.maximalIdeal_eq]; exact Ideal.subset_span (Set.mem_singleton π))
  have hfnot : f π ∉ mB ^ 2 := by
    intro hfdeep
    apply chosenLocalIntegerRing_not_maximalIdeal_le_sq (K := K) (L := L) v₀
    intro z hz
    obtain ⟨x, hx⟩ :=
      chosenGlobalToLocalIntegerRing_exists_approx_mod_maximalIdeal_pow
        (K := K) (L := L) v₀ 2 z
    have hsqle : mB ^ 2 ≤ mB := by
      rw [pow_two]
      exact Ideal.mul_le_left
    have hxerrM : z - f x ∈ mB := hsqle hx
    have hfxM : f x ∈ mB := by
      have h := mB.sub_mem hz hxerrM
      convert h using 1 <;> ring
    have hxM : x ∈ IsLocalRing.maximalIdeal A :=
      (chosenGlobalToLocalIntegerRing_mem_maximalIdeal_iff
        (K := K) (L := L) v₀ x).1 hfxM
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hxM
    obtain ⟨c, rfl⟩ := hxM
    have hfxDeep : f (π * c) ∈ mB ^ 2 := by
      rw [map_mul]
      exact (mB ^ 2).mul_mem_right (f c) hfdeep
    have hzDeep := (mB ^ 2).add_mem hx hfxDeep
    convert hzDeep using 1 <;> ring
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer (f π)).2
  let I : Ideal B := Ideal.span {f π}
  have hIle : I ≤ mB := Ideal.span_le.2 fun z hz => by
    have hz' : z = f π := hz
    rw [hz']
    exact hfm
  by_contra hne
  have hIbot : I ≠ ⊥ := by
    intro hbot
    have hfzero : f π = 0 := by
      have : f π ∈ I := Ideal.subset_span (Set.mem_singleton (f π))
      rw [hbot, Ideal.mem_bot] at this
      exact this
    have hπzero : π = 0 := by
      apply Subtype.ext
      apply (AbsoluteValue.toAlgebraicLocalization
        (HeightOneSpectrum.adicAbv K v₀)
        (chosenFinitePlaceExtension (L := L) v₀).1
        (chosenFinitePlaceExtension (L := L) v₀).2).injective
      exact congrArg Subtype.val hfzero
    exact hπ.ne_zero hπzero
  have hIsq : I ≤ mB ^ 2 :=
    GaloisForLFunctions.HTGeometry.le_maximalIdeal_sq_of_ne hIle
      (fun h => hne h.symm) hIbot
  exact hfnot (hIsq (Ideal.subset_span (Set.mem_singleton (f π))))

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1200000 in
/-- The canonical dense embedding reflects every maximal-ideal power.  Consequently exact
source valuations, including nonmembership at the first excluded depth, survive completion. -/
theorem chosenGlobalToLocalIntegerRing_mem_maximalIdeal_pow_iff
    (v₀ : HeightOneSpectrum (𝓞 K))
    [IsDiscreteValuationRing
      (chosenGlobalValuationRing (K := K) (L := L) v₀)]
    (n : ℕ)
    (x : chosenGlobalValuationRing (K := K) (L := L) v₀) :
    chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x ∈
        IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n ↔
      x ∈ IsLocalRing.maximalIdeal
        (chosenGlobalValuationRing (K := K) (L := L) v₀) ^ n := by
  let A := chosenGlobalValuationRing (K := K) (L := L) v₀
  let B := 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]
  let f : A →+* B := chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmapπ : Irreducible (f π) :=
    chosenGlobalToLocalIntegerRing_map_irreducible
      (K := K) (L := L) v₀ hπ
  rw [GaloisForLFunctions.HTGeometry.mem_maximalIdeal_pow_iff_le_addVal,
    GaloisForLFunctions.HTGeometry.mem_maximalIdeal_pow_iff_le_addVal]
  change (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal B (f x) ↔
    (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal A x
  by_cases hx : x = 0
  · subst x
    simp
  have hmapVal := GaloisForLFunctions.HTGeometry.addVal_map_eq_mul_ramification
    f hπ 1 (by simpa using IsDiscreteValuationRing.addVal_uniformizer hmapπ) x hx
  rw [hmapVal]
  simp

theorem displacement_mem_of_dense_ideal_approximation
    {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal B) (f : A →+* B) (τ : B ≃+* B)
    (happrox : ∀ z : B, ∃ x : A, z - f x ∈ I)
    (hstable : ∀ e : B, e ∈ I → τ e ∈ I)
    (hmain : ∀ x : A, τ (f x) - f x ∈ I)
    (z : B) : τ z - z ∈ I := by
  obtain ⟨x, hx⟩ := happrox z
  let e : B := z - f x
  have he : e ∈ I := hx
  have herror : τ e - e ∈ I := I.sub_mem (hstable e he) he
  have hdecomp : τ z - z = (τ e - e) + (τ (f x) - f x) := by
    dsimp only [e]
    rw [map_sub]
    ring
  rw [hdecomp]
  exact I.add_mem herror (hmain x)

set_option maxHeartbeats 1200000 in
/-- The completed decomposition action intertwines the canonical dense source embedding.  The
identity is coefficient-faithful: the local displacement is literally the image of the global
displacement, not merely congruent to it. -/
theorem chosenLocalIntegerRingAut_chosenGlobalToLocalIntegerRing_sub
    (v₀ : HeightOneSpectrum (𝓞 K))
    (σ : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
      (chosenGlobalValuationRing (K := K) (L := L) v₀))
    (x : chosenGlobalValuationRing (K := K) (L := L) v₀) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let w := chosenFinitePlaceExtension (L := L) v₀
    let τD := localizationRamificationGroups_valuationDecompositionGroupEquiv
      vK (RayClass.adicAbv_isNontrivial v₀) w
        (finitePlaceExtension_nonarchimedean (K := K) (L := L) v₀ w) σ
    let τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ := τD
    chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ
          (chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x) -
        chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x =
      chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ (σ • x - x) := by
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hw := finitePlaceExtension_nonarchimedean (K := K) (L := L) v₀ w
  let τD := localizationRamificationGroups_valuationDecompositionGroupEquiv
    vK (RayClass.adicAbv_isNontrivial v₀) w hw σ
  let τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ := τD
  apply Subtype.ext
  change τ (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L)) -
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L) =
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
      (((σ : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
        (chosenGlobalValuationRing (K := K) (L := L) v₀)) : L ≃ₐ[K] L)
          (x : L) - (x : L))
  rw [map_sub,
    localizationRamificationGroups_valuationDecompositionGroupEquiv_toLocalization]

set_option maxHeartbeats 1200000 in
theorem chosenDecompositionDisplacement_mem_local_of_global
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (σ : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
      (chosenGlobalValuationRing (K := K) (L := L) v₀))
    (hσ : ∀ x : chosenGlobalValuationRing (K := K) (L := L) v₀,
      σ • x - x ∈ IsLocalRing.maximalIdeal
        (chosenGlobalValuationRing (K := K) (L := L) v₀) ^ n)
    (z : 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let w := chosenFinitePlaceExtension (L := L) v₀
    let τD := localizationRamificationGroups_valuationDecompositionGroupEquiv
      vK (RayClass.adicAbv_isNontrivial v₀) w
        (finitePlaceExtension_nonarchimedean (K := K) (L := L) v₀ w) σ
    let τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ := τD
    chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ z - z ∈
      IsLocalRing.maximalIdeal
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n := by
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hw := finitePlaceExtension_nonarchimedean (K := K) (L := L) v₀ w
  let τD := localizationRamificationGroups_valuationDecompositionGroupEquiv
    vK (RayClass.adicAbv_isNontrivial v₀) w hw σ
  let τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ := τD
  let eτ := chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ
  let f := chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀
  let I := IsLocalRing.maximalIdeal
    𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n
  apply displacement_mem_of_dense_ideal_approximation I f eτ
  · exact chosenGlobalToLocalIntegerRing_exists_approx_mod_maximalIdeal_pow
      (K := K) (L := L) v₀ n
  · intro e he
    exact (chosenLocalIntegerRingAut_mem_maximalIdeal_pow_iff
      (K := K) (L := L) v₀ τ n e).2 he
  · intro x
    have hglobal := hσ x
    have hmainMapped : f (σ • x - x) ∈ I :=
      chosenGlobalToLocalIntegerRing_mem_maximalIdeal_pow
        (K := K) (L := L) v₀ n hglobal
    have hcomm : eτ (f x) - f x = f (σ • x - x) :=
      chosenLocalIntegerRingAut_chosenGlobalToLocalIntegerRing_sub
        (K := K) (L := L) v₀ σ x
    rw [hcomm]
    exact hmainMapped

end HilbertRamification
