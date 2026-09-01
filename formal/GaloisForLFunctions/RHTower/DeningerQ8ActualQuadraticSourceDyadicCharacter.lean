import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceLocalConductor
import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceDyadicCompletion
import GaloisForLFunctions.RHTower.DeningerQ8TwoAdicTatePhaseDichotomy
import AlgebraicNumberTheory.Completion.IntegerRingComparison

/-!
# Actual dyadic character of the Q8 quadratic source

The canonical dyadic completion equivalence transports `ℤ₂ˣ` into the
literal source completion.  Genuine local reciprocity kills its level-eight
congruence kernel, so the coefficient-faithful source character descends to
`(ℤ / 8ℤ)ˣ`.  The descended character is even.
-/

namespace RHTower

noncomputable section

open scoped NumberField Pointwise ValuativeRel NNReal
open IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open GlobalClassFieldTheory.Reciprocity
open GaloisForLFunctions.RHTower

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

noncomputable local instance : IsAbelianGalois S K3 :=
  IsAbelianGalois.of_isCyclic _ _

noncomputable local instance q8QuadraticSourceDyadicCharacterChosenLocalGalIsCyclic
    (v : HeightOneSpectrum (𝓞 S)) :
    IsCyclic Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
      ChosenFinitePlaceBaseCompletion (K := S) v) :=
  (MulEquiv.isCyclic (q8QuadraticSourceChosenLocalGalEquiv v)).mp inferInstance

noncomputable local instance q8QuadraticSourceDyadicCharacterChosenLocalIsAbelianGalois
    (v : HeightOneSpectrum (𝓞 S)) :
    IsAbelianGalois
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) :=
  IsAbelianGalois.of_isCyclic _ _

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-- Canonical embedding of rational dyadic units in the literal source completion. -/
noncomputable def q8QuadraticSourcePadicIntegerUnitEmbedding
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    ℤ_[2]ˣ →* (v.adicCompletion S)ˣ :=
  Units.map ((v.adicCompletionIntegers S).subtype.comp
    (q8QuadraticSource_dyadic_padicIntRingEquiv v hv).toRingHom)

@[simp] theorem q8QuadraticSourcePadicIntegerUnitEmbedding_coe
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (u : ℤ_[2]ˣ) :
    ((q8QuadraticSourcePadicIntegerUnitEmbedding v hv u :
        (v.adicCompletion S)ˣ) : v.adicCompletion S) =
      (((q8QuadraticSource_dyadic_padicIntRingEquiv v hv) (u : ℤ_[2]) :
          v.adicCompletionIntegers S) : v.adicCompletion S) :=
  rfl

/-- Level-eight congruence units enter the literal third local higher-unit group. -/
theorem q8QuadraticSourcePadicIntegerUnitEmbedding_mem_localHigherUnitGroup_three
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (u : ℤ_[2]ˣ)
    (hu : fieldOnePadicUnitReduction 2 3 u = 1) :
    q8QuadraticSourcePadicIntegerUnitEmbedding v hv u ∈
      RayClass.localHigherUnitGroup v 3 := by
  let e := q8QuadraticSource_dyadic_padicIntRingEquiv v hv
  let eu : (v.adicCompletionIntegers S).units :=
    (Units.mapEquiv e.toMulEquiv).trans
      (v.adicCompletionIntegers S).toSubmonoid.unitsEquivUnitsType.symm u
  have hsource : (u : ℤ_[2]) - 1 ∈
      IsLocalRing.maximalIdeal ℤ_[2] ^ 3 := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa [fieldOnePadicUnitReduction] using congrArg Units.val hu
  have htarget : e (u : ℤ_[2]) - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers S) ^ 3 := by
    rw [← e.map_one, ← e.map_sub]
    exact (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      e 3 ((u : ℤ_[2]) - 1)).2 hsource
  apply (RayClass.mem_localHigherUnitGroup_iff v 3 _).2
  refine ⟨eu, ?_, ?_⟩
  · rfl
  · apply (RayClass.localHigherUnitMap_eq_one_iff v 3 eu).2
    exact htarget

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- Genuine finite-place Artin reciprocity kills the level-eight source kernel. -/
theorem q8QuadraticSourceChosenFinitePlaceArtin_eq_one_of_reduction_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (u : ℤ_[2]ˣ)
    (hu : fieldOnePadicUnitReduction 2 3 u = 1) :
    chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
      (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) = 1 := by
  let B := ChosenFinitePlaceBaseCompletion (K := S) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v
  let eS := q8QuadraticSource_dyadic_padicIntRingEquiv v hv
  let y : (v.adicCompletionIntegers S).units :=
    (Units.mapEquiv eS.toMulEquiv).trans
      (v.adicCompletionIntegers S).toSubmonoid.unitsEquivUnitsType.symm u
  let eO := finitePlaceCompletionIntegerRingEquiv v
  let eUnits : 𝒪[B]ˣ ≃* (v.adicCompletionIntegers S).units :=
    (Units.mapEquiv eO.toMulEquiv).trans
      (v.adicCompletionIntegers S).toSubmonoid.unitsEquivUnitsType.symm
  let b : 𝒪[B]ˣ := eUnits.symm y
  have hsource : (u : ℤ_[2]) - 1 ∈
      IsLocalRing.maximalIdeal ℤ_[2] ^ 3 := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa [fieldOnePadicUnitReduction] using congrArg Units.val hu
  have htarget : eS (u : ℤ_[2]) - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers S) ^ 3 := by
    rw [← eS.map_one, ← eS.map_sub]
    exact (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      eS 3 ((u : ℤ_[2]) - 1)).2 hsource
  have hb : b ∈ LocalFieldTheory.principalUnits B 3 := by
    rw [LocalFieldTheory.mem_principalUnits_iff]
    apply (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      eO 3 ((b : 𝒪[B]) - 1)).1
    simpa [b, y, eUnits, eO, eS] using htarget
  have hfield :
      (eUnits b : (v.adicCompletion S)ˣ) =
        finitePlaceCompletionUnitsContinuousMulEquiv v
          (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits B b) := by
    apply Units.ext
    rfl
  have hx : q8QuadraticSourcePadicIntegerUnitEmbedding v hv u =
      (eUnits b : (v.adicCompletion S)ˣ) := by
    change (v.adicCompletionIntegers S).units.subtype y = eUnits b
    rw [show eUnits b = y from eUnits.apply_symm_apply y]
    rfl
  have hinput :
      finitePlaceLocalArtinInput v
          (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) =
        LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits B b := by
    let eK := finitePlaceCompletionUnitsContinuousMulEquiv v
    change eK.symm (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) = _
    apply eK.injective
    rw [eK.apply_symm_apply]
    exact hx.trans hfield
  have hub :
      LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits B b ∈
        LocalFieldTheory.fieldPrincipalUnits B 3 :=
    ⟨b, hb, rfl⟩
  have hart :=
    q8QuadraticSourceChosenLocalArtin_eq_one_of_mem_fieldPrincipalUnits_three
      v hv
      (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits B b)
      hub
  have hlocal :
      finitePlaceLocalArtinMonoidHom (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)
          (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) = 1 := by
    rw [finitePlaceLocalArtinMonoidHom_apply_normalized]
    rw [hinput]
    exact hart
  change finitePlaceArtinMonoidHomOfExtension (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
      (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) = 1
  rw [finitePlaceArtinMonoidHomOfExtension_factor, MonoidHom.comp_apply,
    hlocal, map_one]

/-- Pullback of the coefficient-faithful actual source character to `ℤ₂ˣ`. -/
noncomputable def q8QuadraticSourcePadicUnitCharacter
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) : ℤ_[2]ˣ →* ℂˣ :=
  (q8QuadraticSourceFinitePlaceCharacter v).comp
    (q8QuadraticSourcePadicIntegerUnitEmbedding v hv)

theorem fieldOnePadicUnitReduction_ker_le_q8QuadraticSourcePadicUnitCharacter_ker
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    (fieldOnePadicUnitReduction 2 3).ker ≤
      (q8QuadraticSourcePadicUnitCharacter v hv).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  rw [q8QuadraticSourcePadicUnitCharacter, MonoidHom.comp_apply,
    q8QuadraticSourceFinitePlaceCharacter, MonoidHom.comp_apply,
    q8QuadraticSourceChosenFinitePlaceArtin_eq_one_of_reduction_eq_one v hv u hu,
    map_one]

/-- Actual source character factored through `(ℤ / 8ℤ)ˣ`. -/
noncomputable def q8QuadraticSourceZModEightUnitHom
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) : (ZMod 8)ˣ →* ℂˣ :=
  (fieldOnePadicUnitReduction 2 3).liftOfSurjective
    (fieldOnePadicUnitReduction_surjective 2 3)
    ⟨q8QuadraticSourcePadicUnitCharacter v hv,
      fieldOnePadicUnitReduction_ker_le_q8QuadraticSourcePadicUnitCharacter_ker v hv⟩

@[simp] theorem q8QuadraticSourceZModEightUnitHom_reduction
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (u : ℤ_[2]ˣ) :
    q8QuadraticSourceZModEightUnitHom v hv (fieldOnePadicUnitReduction 2 3 u) =
      q8QuadraticSourcePadicUnitCharacter v hv u := by
  simp [q8QuadraticSourceZModEightUnitHom]

/-- Genuine source-derived Dirichlet character modulo eight. -/
noncomputable def q8QuadraticSourceZModEightCharacter
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) : DirichletCharacter ℂ 8 :=
  MulChar.ofUnitHom (q8QuadraticSourceZModEightUnitHom v hv)

theorem q8QuadraticSourcePadicIntegerUnitEmbedding_neg_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourcePadicIntegerUnitEmbedding v hv (-1 : ℤ_[2]ˣ) =
      q8QuadraticSourceNegOneCompletionUnit v := by
  apply Units.ext
  unfold q8QuadraticSourceNegOneCompletionUnit
  rw [IdeleGroup.finiteComponent_principalIdele]
  rw [q8QuadraticSourcePadicIntegerUnitEmbedding_coe]
  change (((q8QuadraticSource_dyadic_padicIntRingEquiv v hv)
      (-1 : ℤ_[2]) : v.adicCompletionIntegers S) : v.adicCompletion S) =
    algebraMap S (v.adicCompletion S) (-1 : S)
  rw [map_neg, map_one, map_neg, map_one]
  rfl

@[simp] theorem q8QuadraticSourcePadicUnitCharacter_neg_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourcePadicUnitCharacter v hv (-1 : ℤ_[2]ˣ) = 1 := by
  rw [q8QuadraticSourcePadicUnitCharacter, MonoidHom.comp_apply,
    q8QuadraticSourcePadicIntegerUnitEmbedding_neg_one v hv]
  exact q8QuadraticSourceFinitePlaceCharacter_neg_one_eq_one v hv

theorem fieldOnePadicUnitReduction_neg_one_two_three :
    fieldOnePadicUnitReduction 2 3 (-1 : ℤ_[2]ˣ) =
      (-1 : (ZMod 8)ˣ) := by
  apply Units.ext
  simp [fieldOnePadicUnitReduction]

@[simp] theorem q8QuadraticSourceZModEightUnitHom_neg_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceZModEightUnitHom v hv (-1 : (ZMod 8)ˣ) = 1 := by
  rw [← fieldOnePadicUnitReduction_neg_one_two_three,
    q8QuadraticSourceZModEightUnitHom_reduction,
    q8QuadraticSourcePadicUnitCharacter_neg_one]

/-- The genuine source-derived level-eight character is even. -/
@[simp] theorem q8QuadraticSourceZModEightCharacter_neg_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceZModEightCharacter v hv (-1 : ZMod 8) = 1 := by
  rw [q8QuadraticSourceZModEightCharacter, ← Units.coe_neg_one,
    MulChar.ofUnitHom_coe, q8QuadraticSourceZModEightUnitHom_neg_one]
  rfl

end

end RHTower
