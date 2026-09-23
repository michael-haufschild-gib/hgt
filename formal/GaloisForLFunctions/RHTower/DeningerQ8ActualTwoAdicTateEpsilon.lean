import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceDyadicCharacter

/-!
# Actual two-adic Tate epsilon of the Q8 source

Filtered local reciprocity supplies a depth-two principal unit whose Artin
image is the literal completed central involution.  Completion transport
pulls that witness back to `ℤ₂ˣ`, where the genuine source character takes
value `-1`.  Thus its even modulo-eight quotient is nontrivial, hence is the
unique even nontrivial character `χ₈`.  The two actual Tate orientations
therefore have product `+1`.
-/

namespace RHTower

noncomputable section

open scoped NumberField Pointwise ValuativeRel NNReal
open IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open GlobalClassFieldTheory.Reciprocity
open HilbertRamification
open GaloisForLFunctions.RHTower

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField
local notation "S" => q8BiquadQuadraticSourceField

local instance deningerQ8ActualTwoAdicTateEpsilonInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance deningerQ8ActualTwoAdicTateEpsilonInst2 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst3 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst4 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst5 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst6 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst7 : FiniteDimensional S K2 := by infer_instance
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst8 : FiniteDimensional S K3 :=
  FiniteDimensional.trans S K2 K3
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst9 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst10 : NumberField S := NumberField.mk
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst11 : NumberField K2 := NumberField.mk
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst12 : NumberField K3 := NumberField.mk
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst13 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst14 : IsGalois S K3 :=
  IsGalois.tower_top_of_isGalois ℚ S K3

noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst15 : IsCyclic deningerQ8ActualCyclicSubgroup := by
  have hq8 : IsCyclic q8CyclicSubgroup :=
    (MulEquiv.isCyclic q8CyclicSourceEquiv).mp inferInstance
  exact (MulEquiv.isCyclic deningerQ8ActualCyclicSubgroupEquiv).mpr hq8

noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst16 : IsCyclic Gal(K3/S) :=
  (MulEquiv.isCyclic q8QuadraticSourceGalEquivCyclicSubgroup).mpr
    (inferInstance : IsCyclic deningerQ8ActualCyclicSubgroup)

noncomputable local instance deningerQ8ActualTwoAdicTateEpsilonInst17 : IsAbelianGalois S K3 :=
  IsAbelianGalois.of_isCyclic _ _

noncomputable local instance q8ActualTwoAdicTateChosenLocalGalIsCyclic
    (v : HeightOneSpectrum (𝓞 S)) :
    IsCyclic Gal(ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v /
      ChosenFinitePlaceBaseCompletion (K := S) v) :=
  (MulEquiv.isCyclic (q8QuadraticSourceChosenLocalGalEquiv v)).mp inferInstance

noncomputable local instance q8ActualTwoAdicTateChosenLocalIsAbelianGalois
    (v : HeightOneSpectrum (𝓞 S)) :
    IsAbelianGalois
      (ChosenFinitePlaceBaseCompletion (K := S) v)
      (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) :=
  IsAbelianGalois.of_isCyclic _ _

local instance deningerQ8ActualTwoAdicTateEpsilonInst18 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- The local-to-global Artin inclusion sends the completed central element
back to the literal source central involution. -/
theorem q8QuadraticSourceFinitePlaceLocalToGlobal_central
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    finitePlaceLocalToGlobalMonoidHom (K := S) (L := K3) v
        (chosenFinitePlaceExtension (L := K3) v)
        (q8QuadraticSourceCentralChosenLocalEquiv v hv) =
      q8QuadraticSourceCentral := by
  let vK := NumberField.HeightOneSpectrum.adicAbv S v
  let w := chosenFinitePlaceExtension (L := K3) v
  let hw := finitePlaceExtension_nonarchimedean (K := S) (L := K3) v w
  let eA :=
    HilbertRamification.localizationRamificationGroups_absoluteValueDecompositionGroupEquiv
      vK (RayClass.adicAbv_isNontrivial v) w hw
  let eD := HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
    vK (RayClass.adicAbv_isNontrivial v) w
  let eL := HilbertRamification.localizationRamificationGroups_localDecompositionGroupEquiv
    vK (RayClass.adicAbv_isNontrivial v) w hw
  let sigma := q8QuadraticSourceCentralChosenDecomposition v hv
  have hq : q8QuadraticSourceChosenLocalGalEquiv v sigma =
      eD (eA.symm sigma) := by
    change eL.symm (eL (eD (eA.symm sigma))) = eD (eA.symm sigma)
    exact eL.symm_apply_apply _
  rw [← q8QuadraticSourceChosenLocalGalEquiv_central v hv, hq]
  change ((((HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK (RayClass.adicAbv_isNontrivial v) w).symm
        (eD (eA.symm sigma)) : absoluteValueDecompositionGroup S w.1) :
      Gal(K3/S))) = q8QuadraticSourceCentral
  rw [show (HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK (RayClass.adicAbv_isNontrivial v) w).symm
        (eD (eA.symm sigma)) = eA.symm sigma from eD.symm_apply_apply _]
  rfl

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
/-- The depth-two principal-unit image contains the literal completed
central involution, with an explicit existential preimage. -/
theorem q8QuadraticSourceCentral_exists_localPrincipalUnit_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    ∃ x : (ChosenFinitePlaceBaseCompletion (K := S) v)ˣ,
      x ∈ LocalFieldTheory.fieldPrincipalUnits
          (ChosenFinitePlaceBaseCompletion (K := S) v) 2 ∧
        LocalClassFieldTheory.abelianLocalArtinMonoidHom
            (ChosenFinitePlaceBaseCompletion (K := S) v)
            (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) x =
          q8QuadraticSourceCentralChosenLocalEquiv v hv := by
  let B := ChosenFinitePlaceBaseCompletion (K := S) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v
  have hfiltered := LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity
    B E (2 : ℝ) (by norm_num)
  have hstep : LocalClassFieldTheory.artinPrincipalUnitStepGroup B E (2 : ℝ) =
      q8QuadraticSourceCentralChosenLocalSubgroup v hv :=
    hfiltered.trans (q8QuadraticSourceChosenLocalUpper_two v hv)
  have hcentral : q8QuadraticSourceCentralChosenLocalEquiv v hv ∈
      q8QuadraticSourceCentralChosenLocalSubgroup v hv :=
    Subgroup.mem_zpowers _
  have himage : q8QuadraticSourceCentralChosenLocalEquiv v hv ∈
      LocalClassFieldTheory.artinPrincipalUnitGroup B E 2 := by
    rw [← hstep] at hcentral
    simpa [LocalClassFieldTheory.artinPrincipalUnitStepGroup,
      RamificationTheory.natCeilStepFiltration] using hcentral
  rcases himage with ⟨x, hx, hart⟩
  exact ⟨x, hx, hart⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- Some rational dyadic unit maps to the source central coefficient `-1`.
This is the nontriviality witness missing from mere conductor descent. -/
theorem q8QuadraticSourcePadicUnitCharacter_exists_eq_neg_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    ∃ u : ℤ_[2]ˣ,
      q8QuadraticSourcePadicUnitCharacter v hv u = (-1 : ℂˣ) := by
  let B := ChosenFinitePlaceBaseCompletion (K := S) v
  obtain ⟨x, hx, hart⟩ :=
    q8QuadraticSourceCentral_exists_localPrincipalUnit_two v hv
  rcases hx with ⟨b, _hb, hbx⟩
  let eO := finitePlaceCompletionIntegerRingEquiv v
  let eOUnits : 𝒪[B]ˣ ≃* (v.adicCompletionIntegers S).units :=
    (Units.mapEquiv eO.toMulEquiv).trans
      (v.adicCompletionIntegers S).toSubmonoid.unitsEquivUnitsType.symm
  let eS := q8QuadraticSource_dyadic_padicIntRingEquiv v hv
  let eSUnits : ℤ_[2]ˣ ≃* (v.adicCompletionIntegers S).units :=
    (Units.mapEquiv eS.toMulEquiv).trans
      (v.adicCompletionIntegers S).toSubmonoid.unitsEquivUnitsType.symm
  let u : ℤ_[2]ˣ := eSUnits.symm (eOUnits b)
  have hembed : q8QuadraticSourcePadicIntegerUnitEmbedding v hv u =
      (eOUnits b : (v.adicCompletion S)ˣ) := by
    apply Units.ext
    change (((eSUnits u : (v.adicCompletionIntegers S).units) :
      (v.adicCompletion S)ˣ) : v.adicCompletion S) =
        (((eOUnits b : (v.adicCompletionIntegers S).units) :
          (v.adicCompletion S)ˣ) : v.adicCompletion S)
    rw [show eSUnits u = eOUnits b from eSUnits.apply_symm_apply (eOUnits b)]
  have hfield :
      (eOUnits b : (v.adicCompletion S)ˣ) =
        finitePlaceCompletionUnitsContinuousMulEquiv v
          (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits B b) := by
    apply Units.ext
    rfl
  have hinput : finitePlaceLocalArtinInput v
      (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) = x := by
    let eK := finitePlaceCompletionUnitsContinuousMulEquiv v
    change eK.symm (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) = x
    apply eK.injective
    rw [eK.apply_symm_apply, hembed, hfield]
    exact congrArg eK hbx
  have hlocal :
      finitePlaceLocalArtinMonoidHom (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)
          (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) =
        q8QuadraticSourceCentralChosenLocalEquiv v hv := by
    rw [finitePlaceLocalArtinMonoidHom_apply_normalized, hinput]
    exact hart
  have hglobal :
      chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
          (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) =
        q8QuadraticSourceCentral := by
    change finitePlaceArtinMonoidHomOfExtension (K := S) (L := K3) v
        (chosenFinitePlaceExtension (L := K3) v)
        (q8QuadraticSourcePadicIntegerUnitEmbedding v hv u) = _
    rw [finitePlaceArtinMonoidHomOfExtension_factor, MonoidHom.comp_apply,
      hlocal, q8QuadraticSourceFinitePlaceLocalToGlobal_central v hv]
  refine ⟨u, ?_⟩
  rw [q8QuadraticSourcePadicUnitCharacter, MonoidHom.comp_apply,
    q8QuadraticSourceFinitePlaceCharacter, MonoidHom.comp_apply, hglobal]
  exact q8QuadraticSourceCharacter_central

/-- The descended source character takes value `-1` on an actual
modulo-eight unit. -/
theorem q8QuadraticSourceZModEightCharacter_exists_eq_neg_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    ∃ a : (ZMod 8)ˣ,
      q8QuadraticSourceZModEightCharacter v hv (a : ZMod 8) = (-1 : ℂ) := by
  obtain ⟨u, hu⟩ :=
    q8QuadraticSourcePadicUnitCharacter_exists_eq_neg_one v hv
  refine ⟨fieldOnePadicUnitReduction 2 3 u, ?_⟩
  rw [q8QuadraticSourceZModEightCharacter, MulChar.ofUnitHom_coe,
    q8QuadraticSourceZModEightUnitHom_reduction, hu]
  rfl

/-- The genuine source-derived modulo-eight character is nontrivial. -/
theorem q8QuadraticSourceZModEightCharacter_ne_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceZModEightCharacter v hv ≠ 1 := by
  intro hone
  obtain ⟨a, ha⟩ :=
    q8QuadraticSourceZModEightCharacter_exists_eq_neg_one v hv
  have hval := congrArg
    (fun chi : DirichletCharacter ℂ 8 => chi (a : ZMod 8)) hone
  have honeval : (1 : DirichletCharacter ℂ 8) (a : ZMod 8) = 1 :=
    MulChar.one_apply a.isUnit
  rw [honeval, ha] at hval
  norm_num at hval

/-- Exhaustive structural classification of units modulo eight. -/
theorem zmodEight_unit_eq_one_or_three_or_five_or_seven
    (x : (ZMod 8)ˣ) :
    (x : ZMod 8) = 1 ∨ (x : ZMod 8) = 3 ∨
      (x : ZMod 8) = 5 ∨ (x : ZMod 8) = 7 := by
  have hlt := ZMod.val_lt (x : ZMod 8)
  interval_cases hval : (x : ZMod 8).val
  · have hx : (x : ZMod 8) = 0 := (ZMod.val_eq_zero _).mp hval
    exact ((by decide : ¬ IsUnit (0 : ZMod 8)) (hx ▸ x.isUnit)).elim
  · exact Or.inl ((ZMod.val_eq_one (by norm_num) _).mp hval)
  · have hx : (x : ZMod 8) = 2 := by
      apply ZMod.val_injective 8
      rw [hval]
      exact (ZMod.val_cast_of_lt (by norm_num)).symm
    exact ((by decide : ¬ IsUnit (2 : ZMod 8)) (hx ▸ x.isUnit)).elim
  · exact Or.inr (Or.inl (by
      apply ZMod.val_injective 8
      rw [hval]
      exact (ZMod.val_cast_of_lt (by norm_num)).symm))
  · have hx : (x : ZMod 8) = 4 := by
      apply ZMod.val_injective 8
      rw [hval]
      exact (ZMod.val_cast_of_lt (by norm_num)).symm
    exact ((by decide : ¬ IsUnit (4 : ZMod 8)) (hx ▸ x.isUnit)).elim
  · exact Or.inr (Or.inr (Or.inl (by
      apply ZMod.val_injective 8
      rw [hval]
      exact (ZMod.val_cast_of_lt (by norm_num)).symm)))
  · have hx : (x : ZMod 8) = 6 := by
      apply ZMod.val_injective 8
      rw [hval]
      exact (ZMod.val_cast_of_lt (by norm_num)).symm
    exact ((by decide : ¬ IsUnit (6 : ZMod 8)) (hx ▸ x.isUnit)).elim
  · exact Or.inr (Or.inr (Or.inr (by
      apply ZMod.val_injective 8
      rw [hval]
      exact (ZMod.val_cast_of_lt (by norm_num)).symm)))

/-- Evenness and nontriviality alone classify a complex character modulo
eight; no separate quadraticity or primitivity hypothesis is needed. -/
theorem evenNontrivialZModEightCharacter_eq_quadraticCharacterEight
    (chi : DirichletCharacter ℂ 8)
    (heven : chi (-1 : ZMod 8) = 1)
    (hne : chi ≠ 1) :
    chi = quadraticCharacterEight := by
  have h7 : chi (7 : ZMod 8) = 1 := by
    have hneg : (-1 : ZMod 8) = (7 : ZMod 8) := by
      change ((-1 : ℤ) : ZMod 8) = ((7 : ℤ) : ZMod 8)
      rw [ZMod.intCast_eq_intCast_iff']
      norm_num
    rw [← hneg]
    exact heven
  have h35 : chi (3 : ZMod 8) * chi (5 : ZMod 8) = 1 := by
    rw [← map_mul]
    norm_num
    exact h7
  have h3sq : chi (3 : ZMod 8) * chi (3 : ZMod 8) = 1 := by
    rw [← map_mul]
    have h33 : (3 : ZMod 8) * (3 : ZMod 8) = 1 := by decide
    rw [h33, MulChar.map_one]
  have hfactor :
      (chi (3 : ZMod 8) - 1) * (chi (3 : ZMod 8) + 1) = 0 := by
    calc
      _ = chi (3 : ZMod 8) * chi (3 : ZMod 8) - 1 := by ring
      _ = 0 := by rw [h3sq]; ring
  have h3 : chi (3 : ZMod 8) = -1 := by
    rcases mul_eq_zero.mp hfactor with honeFactor | hnegFactor
    · have hone : chi (3 : ZMod 8) = 1 := sub_eq_zero.mp honeFactor
      exfalso
      have h5 : chi (5 : ZMod 8) = 1 := by
        rw [hone, one_mul] at h35
        exact h35
      apply hne
      apply MulChar.ext
      intro x
      rw [MulChar.one_apply_coe]
      rcases zmodEight_unit_eq_one_or_three_or_five_or_seven x with
        hx | hx | hx | hx
      · rw [hx, MulChar.map_one]
      · simpa [hx] using hone
      · simpa [hx] using h5
      · simpa [hx] using h7
    · calc
        chi (3 : ZMod 8) = chi (3 : ZMod 8) + 1 - 1 := by ring
        _ = 0 - 1 := by rw [hnegFactor]
        _ = -1 := by ring
  have h5 : chi (5 : ZMod 8) = -1 := by
    rw [h3, neg_mul] at h35
    have h := congrArg Neg.neg h35
    simpa using h
  apply MulChar.ext
  intro x
  rcases zmodEight_unit_eq_one_or_three_or_five_or_seven x with
    hx | hx | hx | hx
  · change chi (x : ZMod 8) = quadraticCharacterEight (x : ZMod 8)
    rw [hx, MulChar.map_one, MulChar.map_one]
  · change chi (x : ZMod 8) = quadraticCharacterEight (x : ZMod 8)
    rw [hx, h3]
    norm_num [quadraticCharacterEight, ZMod.χ₈]
  · change chi (x : ZMod 8) = quadraticCharacterEight (x : ZMod 8)
    rw [hx, h5]
    norm_num [quadraticCharacterEight, ZMod.χ₈]
  · change chi (x : ZMod 8) = quadraticCharacterEight (x : ZMod 8)
    rw [hx, h7]
    norm_num [quadraticCharacterEight, ZMod.χ₈]

/-- The genuine dyadic source character is exactly the even conductor-eight
quadratic character. -/
theorem q8QuadraticSourceZModEightCharacter_eq_quadraticCharacterEight
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceZModEightCharacter v hv = quadraticCharacterEight :=
  evenNontrivialZModEightCharacter_eq_quadraticCharacterEight
    (q8QuadraticSourceZModEightCharacter v hv)
    (q8QuadraticSourceZModEightCharacter_neg_one v hv)
    (q8QuadraticSourceZModEightCharacter_ne_one v hv)

theorem q8QuadraticSourceZModEightCharacter_isPrimitive
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    DirichletCharacter.IsPrimitive
      (q8QuadraticSourceZModEightCharacter v hv) := by
  rw [q8QuadraticSourceZModEightCharacter_eq_quadraticCharacterEight v hv]
  exact quadraticCharacterEight_isPrimitive

theorem q8QuadraticSourceZModEightCharacter_isQuadratic
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    (q8QuadraticSourceZModEightCharacter v hv).IsQuadratic := by
  rw [q8QuadraticSourceZModEightCharacter_eq_quadraticCharacterEight v hv]
  exact quadraticCharacterEight_isQuadratic

/-- Actual primitive angular character selected by the Q8 source at two. -/
noncomputable def q8ActualTwoPrimitiveTateCharacter
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    FieldOnePadicPrimitiveAngularCharacter 2 3 :=
  ⟨q8QuadraticSourceZModEightCharacter v hv,
    q8QuadraticSourceZModEightCharacter_isPrimitive v hv⟩

theorem q8ActualTwoPrimitiveTateCharacter_eq_even
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8ActualTwoPrimitiveTateCharacter v hv =
      q8TwoAdicEvenPrimitiveTateCharacter := by
  apply Subtype.ext
  exact q8QuadraticSourceZModEightCharacter_eq_quadraticCharacterEight v hv

/-- Analytic local Tate epsilon of the actual dyadic source orientation. -/
noncomputable def q8ActualTwoLocalTateEpsilon
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) : ℂ :=
  fieldOnePadicRamifiedTatePhase 2 3
    (q8ActualTwoPrimitiveTateCharacter v hv) 1

/-- Analytic local Tate epsilon of the inverse dyadic source orientation. -/
noncomputable def q8ActualTwoInverseLocalTateEpsilon
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) : ℂ :=
  fieldOnePadicRamifiedTatePhase 2 3
    (fieldOnePadicPrimitiveAngularCharacterInv 2 3
      (q8ActualTwoPrimitiveTateCharacter v hv)) 1

/-- The actual two dyadic source orientations have Tate epsilon product `+1`. -/
theorem q8ActualTwoLocalTateEpsilon_mul_inverse_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8ActualTwoLocalTateEpsilon v hv *
      q8ActualTwoInverseLocalTateEpsilon v hv = 1 := by
  rw [q8ActualTwoLocalTateEpsilon,
    q8ActualTwoInverseLocalTateEpsilon,
    q8ActualTwoPrimitiveTateCharacter_eq_even v hv]
  simpa using q8TwoAdicEvenTatePhase_pair_eq_one 1

end

end RHTower
