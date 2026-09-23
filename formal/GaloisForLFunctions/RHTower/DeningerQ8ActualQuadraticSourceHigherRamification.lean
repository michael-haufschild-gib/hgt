import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceArtin
import GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicHigherRamification
import GaloisForLFunctions.HTGeometry.DedekindResidueFieldAtPlace
import GaloisForLFunctions.HTGeometry.ChosenHigherRamificationTransport
import AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
import RamificationTheory.HilbertRamification.LocalizationRamificationGroups

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

local instance deningerQ8ActualQuadraticSourceHigherRamificationInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance deningerQ8ActualQuadraticSourceHigherRamificationInst2 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst3 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst4 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst5 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst6 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst7 : FiniteDimensional S K2 := by infer_instance
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst8 : FiniteDimensional S K3 :=
  FiniteDimensional.trans S K2 K3
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst9 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst10 : NumberField S := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst11 : NumberField K2 := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst12 : NumberField K3 := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst13 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
noncomputable local instance deningerQ8ActualQuadraticSourceHigherRamificationInst14 : IsGalois S K3 :=
  IsGalois.tower_top_of_isGalois ℚ S K3
noncomputable local instance q8SourceFieldAction :
    MulSemiringAction Gal(K3/S) K3 := inferInstance
noncomputable local instance q8SourceIsGaloisGroup :
    IsGaloisGroup Gal(K3/S) S K3 := IsGaloisGroup.of_isGalois S K3
noncomputable local instance q8SourceIntegralAction :
    MulSemiringAction Gal(K3/S) (𝓞 K3) := inferInstance
noncomputable local instance q8RatFieldAction :
    MulSemiringAction Gal(K3/ℚ) K3 := inferInstance
noncomputable local instance q8RatIsGaloisGroup :
    IsGaloisGroup Gal(K3/ℚ) ℚ K3 := IsGaloisGroup.of_isGalois ℚ K3
noncomputable local instance q8RatIntegralAction :
    MulSemiringAction Gal(K3/ℚ) (𝓞 K3) := inferInstance

noncomputable def q8QuadraticSourceCentral : Gal(K3/S) :=
  q8QuadraticSourceGalEquivCyclicSubgroup.symm
    ⟨q8CAlgEquiv, by
      rw [deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY,
        MulAction.mem_stabilizer_iff]
      change q8CAlgEquiv deningerQ8RootNumberNegOneTopY =
        deningerQ8RootNumberNegOneTopY
      rw [q8CAlgEquiv_apply, q8C_topY]⟩

theorem q8QuadraticSourceRestrictHom_central :
    q8QuadraticSourceRestrictHom q8QuadraticSourceCentral =
      (⟨q8CAlgEquiv, by
        rw [deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY,
          MulAction.mem_stabilizer_iff]
        change q8CAlgEquiv deningerQ8RootNumberNegOneTopY =
          deningerQ8RootNumberNegOneTopY
        rw [q8CAlgEquiv_apply, q8C_topY]⟩ :
        deningerQ8ActualCyclicSubgroup) := by
  exact q8QuadraticSourceGalEquivCyclicSubgroup.apply_symm_apply _

theorem q8QuadraticSourceCentral_restrictScalars :
    q8QuadraticSourceCentral.restrictScalars ℚ = q8CAlgEquiv := by
  have h := congrArg Subtype.val q8QuadraticSourceRestrictHom_central
  exact h

/-- The coefficient-faithful quartic source character sees the actual central involution as `-1`.
This is the exact nontriviality needed at every occupied dyadic lower break. -/
theorem q8QuadraticSourceCharacter_central :
    q8QuadraticSourceCharacter q8QuadraticSourceCentral = (-1 : ℂˣ) := by
  rw [q8QuadraticSourceCharacter, MonoidHom.comp_apply]
  rw [deningerQ8ActualCyclicSubgroupCharacter, MonoidHom.comp_apply]
  have hmap : deningerQ8ActualCyclicSubgroupEquiv
      (q8QuadraticSourceRestrictHom q8QuadraticSourceCentral) =
      q8CyclicSourceEquiv (Multiplicative.ofAdd (2 : ZMod 4)) := by
    apply Subtype.ext
    change deningerQ8RootNumberNegOne_galoisEquivQ8
        (q8QuadraticSourceRestrictHom q8QuadraticSourceCentral).1 =
      QuaternionGroup.a (2 : ZMod 4)
    rw [q8QuadraticSourceRestrictHom_central,
      deningerQ8_galoisEquiv_q8C]
  change q8CyclicSubgroupCharacter
      (deningerQ8ActualCyclicSubgroupEquiv
        (q8QuadraticSourceRestrictHom q8QuadraticSourceCentral)) =
    (-1 : ℂˣ)
  rw [hmap, q8CyclicSourceEquiv_apply]
  rw [q8CyclicSubgroupCharacter_apply]
  apply Units.ext
  rw [q8OrderFourCharacter_apply]
  have hval : (2 : ZMod 4).val = 2 := by
    exact ZMod.val_natCast_of_lt (n := 4) (a := 2) (by omega)
  rw [hval]
  norm_num [Complex.I_mul_I]

/-- The actual order-two lower subgroup inside the quartic quadratic-source Galois group. -/
abbrev q8QuadraticSourceCentralSubgroup : Subgroup Gal(K3/S) :=
  Subgroup.zpowers q8QuadraticSourceCentral

theorem q8QuadraticSource_lowerRamificationGroup_le_central
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n ≤
      q8QuadraticSourceCentralSubgroup := by
  intro g hg
  have hratC : (q8QuadraticSourceRestrictHom g).1 ∈
      deningerQ8ActualCentralSubgroup := by
    have hprof := q8Literal_two_lowerRamificationGroup_profile P hPtwo n
    rw [if_pos hn] at hprof
    rw [← hprof]
    intro x
    exact hg x
  rcases Subgroup.mem_zpowers_iff.mp hratC with ⟨k, hk⟩
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  apply q8QuadraticSourceRestrictHom_injective
  rw [map_zpow, q8QuadraticSourceRestrictHom_central]
  apply Subtype.ext
  exact hk

/-- The actual central source involution survives through lower level two. -/
theorem q8QuadraticSourceCentral_mem_lowerRamificationGroup_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    q8QuadraticSourceCentral ∈
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P 2 := by
  have hrat := q8Literal_centralInvolution_mem_lowerRamificationGroup_two
    P hPtwo
  intro x
  have heq : q8QuadraticSourceCentral • x = q8CAlgEquiv • x := by
    apply Subtype.ext
    exact DFunLike.congr_fun q8QuadraticSourceCentral_restrictScalars (x : K3)
  rw [heq]
  exact hrat x

/-- Every occupied source lower group is exactly the actual central order-two subgroup. -/
theorem q8QuadraticSource_lowerRamificationGroup_eq_central_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n =
      q8QuadraticSourceCentralSubgroup := by
  apply le_antisymm
  · exact q8QuadraticSource_lowerRamificationGroup_le_central P hPtwo n hn
  · rw [Subgroup.zpowers_le]
    have hle :=
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_antitone
        (G := Gal(K3/S)) P (show n ≤ 2 from hn)
    exact hle (q8QuadraticSourceCentral_mem_lowerRamificationGroup_two P hPtwo)

/-- The quadratic-source lower filtration is trivial from level three onward. -/
theorem q8QuadraticSource_lowerRamificationGroup_eq_bot_of_three_le
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : 3 ≤ n) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n = ⊥ := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_bot]
    have hprof := q8Literal_two_lowerRamificationGroup_profile P hPtwo n
    rw [if_neg (by omega)] at hprof
    apply q8QuadraticSourceRestrictHom_injective
    apply Subtype.ext
    have hrestrict : (q8QuadraticSourceRestrictHom g).1 = 1 := by
      rw [← Subgroup.mem_bot]
      rw [← hprof]
      intro x
      exact hg x
    simpa using hrestrict
  · exact bot_le

/-- Complete lower-numbering profile on the actual quartic quadratic source. -/
theorem q8QuadraticSource_lowerRamificationGroup_profile
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n =
      if n ≤ 2 then q8QuadraticSourceCentralSubgroup else ⊥ := by
  by_cases hn : n ≤ 2
  · rw [if_pos hn]
    exact q8QuadraticSource_lowerRamificationGroup_eq_central_of_le_two
      P hPtwo n hn
  · rw [if_neg hn]
    exact q8QuadraticSource_lowerRamificationGroup_eq_bot_of_three_le
      P hPtwo n (by omega)

theorem q8QuadraticSourceCentral_orderOf :
    orderOf q8QuadraticSourceCentral = 2 := by
  calc
    orderOf q8QuadraticSourceCentral =
        orderOf (q8QuadraticSourceRestrictHom q8QuadraticSourceCentral) :=
      (orderOf_injective q8QuadraticSourceRestrictHom
        q8QuadraticSourceRestrictHom_injective _).symm
    _ = orderOf (q8QuadraticSourceRestrictHom q8QuadraticSourceCentral).1 :=
      (orderOf_injective deningerQ8ActualCyclicSubgroup.subtype
        Subtype.coe_injective _).symm
    _ = orderOf q8CAlgEquiv := by
      exact congrArg orderOf
        (congrArg Subtype.val q8QuadraticSourceRestrictHom_central)
    _ = 2 := deningerQ8ActualCentralInvolution_orderOf

theorem q8QuadraticSourceCentralSubgroup_natCard :
    Nat.card q8QuadraticSourceCentralSubgroup = 2 := by
  rw [Nat.card_zpowers, q8QuadraticSourceCentral_orderOf]

/-- The coefficient-faithful source character has no fixed line under its actual central break. -/
theorem q8QuadraticSourceCharacter_central_invariants_eq_bot :
    Representation.invariants
      ((GaloisForLFunctions.linearCharacterRepresentation
        q8QuadraticSourceCharacter).comp
          q8QuadraticSourceCentralSubgroup.subtype) = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  rw [Submodule.mem_bot]
  have hcfix := hz
    ⟨q8QuadraticSourceCentral, Subgroup.mem_zpowers _⟩
  change (q8QuadraticSourceCharacter q8QuadraticSourceCentral : ℂ) * z = z at hcfix
  rw [q8QuadraticSourceCharacter_central] at hcfix
  have hzneg : -z = z := by simpa using hcfix
  have htwo : (2 : ℂ) * z = 0 := by
    calc
      (2 : ℂ) * z = z + z := by ring
      _ = -z + z := by rw [hzneg]
      _ = 0 := neg_add_cancel z
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem q8QuadraticSourceCharacter_lower_invariants_eq_bot_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    Representation.invariants
      ((GaloisForLFunctions.linearCharacterRepresentation
        q8QuadraticSourceCharacter).comp
          (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
            (G := Gal(K3/S)) P n).subtype) = ⊥ := by
  rw [q8QuadraticSource_lowerRamificationGroup_eq_central_of_le_two
    P hPtwo n hn]
  exact q8QuadraticSourceCharacter_central_invariants_eq_bot

theorem q8QuadraticSourceCharacter_lowerArtinCodimension_eq_one_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinCodimension
      (GaloisForLFunctions.linearCharacterRepresentation
        q8QuadraticSourceCharacter)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n) = 1 := by
  have hinv := q8QuadraticSourceCharacter_lower_invariants_eq_bot_of_le_two
    P hPtwo n hn
  unfold GaloisForLFunctions.HTGeometry.Representation.lowerArtinCodimension
  rw [hinv]
  simp

theorem q8QuadraticSource_lowerRamificationGroup_natCard_eq_two_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    Nat.card
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n) = 2 := by
  rw [q8QuadraticSource_lowerRamificationGroup_eq_central_of_le_two
      P hPtwo n hn,
    q8QuadraticSourceCentralSubgroup_natCard]

/-- Exact occupied source Artin term: one at each lower level zero, one, and two. -/
theorem q8QuadraticSourceCharacter_lowerArtinTerm_eq_one_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
      (GaloisForLFunctions.linearCharacterRepresentation
        q8QuadraticSourceCharacter)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P 0)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n) = 1 := by
  unfold GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
  rw [q8QuadraticSource_lowerRamificationGroup_natCard_eq_two_of_le_two
      P hPtwo n hn,
    q8QuadraticSource_lowerRamificationGroup_natCard_eq_two_of_le_two
      P hPtwo 0 (by omega),
    q8QuadraticSourceCharacter_lowerArtinCodimension_eq_one_of_le_two
      P hPtwo n hn]
  norm_num

theorem q8QuadraticSourceCharacter_lowerArtinTerm_eq_zero_of_three_le
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : 3 ≤ n) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
      (GaloisForLFunctions.linearCharacterRepresentation
        q8QuadraticSourceCharacter)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P 0)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n) = 0 := by
  rw [q8QuadraticSource_lowerRamificationGroup_eq_bot_of_three_le
    P hPtwo n hn]
  exact GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm_bot _ _

theorem q8QuadraticSourceCharacter_lowerArtinTerm_profile
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
      (GaloisForLFunctions.linearCharacterRepresentation
        q8QuadraticSourceCharacter)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P 0)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n) = if n ≤ 2 then 1 else 0 := by
  by_cases hn : n ≤ 2
  · rw [if_pos hn]
    exact q8QuadraticSourceCharacter_lowerArtinTerm_eq_one_of_le_two
      P hPtwo n hn
  · rw [if_neg hn]
    exact q8QuadraticSourceCharacter_lowerArtinTerm_eq_zero_of_three_le
      P hPtwo n (by omega)

/-- The actual coefficient-faithful quadratic-source character has exact dyadic Artin conductor
three. Thus its multiplicative conductor exponent is three, i.e. conductor norm `2^(3 : ℕ) = 8`. -/
theorem q8QuadraticSourceCharacter_lowerArtinConductor_eq_three
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinConductorUpTo
      (GaloisForLFunctions.linearCharacterRepresentation
        q8QuadraticSourceCharacter)
      (fun n => GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := Gal(K3/S)) P n) 4 = 3 := by
  unfold GaloisForLFunctions.HTGeometry.Representation.lowerArtinConductorUpTo
  norm_num [Finset.sum_range_succ,
    q8QuadraticSourceCharacter_lowerArtinTerm_eq_one_of_le_two P hPtwo,
    q8QuadraticSourceCharacter_lowerArtinTerm_eq_zero_of_three_le P hPtwo]

theorem q8FinitePlaceExtensionCentre_two_mem
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    (2 : 𝓞 K3) ∈
      (finitePlaceExtensionCentre (K := S) (L := K3) v
        (chosenFinitePlaceExtension (L := K3) v)).asIdeal := by
  let w := chosenFinitePlaceExtension (L := K3) v
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v w
  have hPover : P.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver (K := S) (L := K3) v w
  change algebraMap (𝓞 S) (𝓞 K3) (2 : 𝓞 S) ∈ P.asIdeal
  rw [← Ideal.mem_comap]
  change (2 : 𝓞 S) ∈ P.asIdeal.under (𝓞 S)
  rw [← hPover.over]
  exact hv

/-- At a chosen dyadic source place, every source automorphism fixes the chosen top prime. -/
theorem q8QuadraticSource_chosenPrime_stabilizer_eq_top
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let P := finitePlaceExtensionCentre (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
    MulAction.stabilizer Gal(K3/S) P.asIdeal = ⊤ := by
  dsimp only
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  have hPtwo := q8FinitePlaceExtensionCentre_two_mem v hv
  apply top_unique
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  have hrat :=
    (q8Literal_two_decomposition_eq_cyclicSource P.asIdeal hPtwo).symm.le
      (q8QuadraticSourceRestrictHom g).2
  rw [MulAction.mem_stabilizer_iff] at hrat
  exact hrat

/-- At a chosen dyadic source place, inertia is literally the source central subgroup. -/
theorem q8QuadraticSource_chosenPrime_inertia_eq_central
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let P := finitePlaceExtensionCentre (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
    P.asIdeal.inertia Gal(K3/S) = q8QuadraticSourceCentralSubgroup := by
  dsimp only
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  have hPtwo := q8FinitePlaceExtensionCentre_two_mem v hv
  have hprof := q8QuadraticSource_lowerRamificationGroup_eq_central_of_le_two
    P.asIdeal hPtwo 0 (by omega)
  rw [GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_eq_lowerRamificationGroup,
    GaloisForLFunctions.HTGeometry.Ideal.lowerRamificationGroup_zero] at hprof
  exact hprof

theorem q8QuadraticSource_chosenPrime_stabilizer_natCard_eq_four
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let P := finitePlaceExtensionCentre (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
    Nat.card (MulAction.stabilizer Gal(K3/S) P.asIdeal) = 4 := by
  dsimp only
  rw [q8QuadraticSource_chosenPrime_stabilizer_eq_top v hv,
    Subgroup.card_top, IsGalois.card_aut_eq_finrank,
    q8BiquadQuadraticSource_top_finrank]

theorem q8QuadraticSource_chosenPrime_inertia_natCard_eq_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let P := finitePlaceExtensionCentre (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
    Nat.card (P.asIdeal.inertia Gal(K3/S)) = 2 := by
  dsimp only
  rw [q8QuadraticSource_chosenPrime_inertia_eq_central v hv,
    q8QuadraticSourceCentralSubgroup_natCard]

/-- The chosen top prime has residue degree two over the dyadic source prime. -/
theorem q8QuadraticSource_chosenPrime_relative_inertiaDeg_eq_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let P := finitePlaceExtensionCentre (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
    P.asIdeal.inertiaDeg (𝓞 S) = 2 := by
  dsimp only
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  letI : P.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
  have hcard := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := Gal(K3/S)) v.asIdeal P.asIdeal
  rw [q8QuadraticSource_chosenPrime_stabilizer_natCard_eq_four v hv,
    q8QuadraticSource_chosenPrime_inertia_natCard_eq_two v hv] at hcard
  change P.asIdeal.inertiaDeg (𝓞 S) = 2
  omega

/-- The chosen top prime has ramification index two over the dyadic source prime. -/
theorem q8QuadraticSource_chosenPrime_relative_ramificationIdx_eq_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let P := finitePlaceExtensionCentre (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
    P.asIdeal.ramificationIdx (𝓞 S) = 2 := by
  dsimp only
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  letI : P.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
  calc
    P.asIdeal.ramificationIdx (𝓞 S) =
        Ideal.ramificationIdxIn v.asIdeal (𝓞 K3) :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx
        v.asIdeal P.asIdeal Gal(K3/S)).symm
    _ = Nat.card (P.asIdeal.inertia Gal(K3/S)) :=
      (Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal P.asIdeal).symm
    _ = 2 := q8QuadraticSource_chosenPrime_inertia_natCard_eq_two v hv

/-- Every dyadic prime of the quadratic source has residue degree one over `ℚ`. -/
theorem q8QuadraticSource_dyadic_inertiaDeg_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    v.asIdeal.inertiaDeg ℤ = 1 := by
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  letI : P.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
  have hPtwo := q8FinitePlaceExtensionCentre_two_mem v hv
  have htower := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P.asIdeal
  rw [q8Literal_two_inertiaDeg_eq_two P.asIdeal hPtwo,
    q8QuadraticSource_chosenPrime_relative_inertiaDeg_eq_two v hv] at htower
  have hpos := Ideal.inertiaDeg_pos v.asIdeal ℤ
  omega

/-- Every dyadic prime of the quadratic source is unramified over `ℚ`. -/
theorem q8QuadraticSource_dyadic_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 := by
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  letI : P.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v)
  have hPtwo := q8FinitePlaceExtensionCentre_two_mem v hv
  have htower := Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P.asIdeal
  rw [q8Literal_two_ramificationIdx_eq_two P.asIdeal hPtwo,
    q8QuadraticSource_chosenPrime_relative_ramificationIdx_eq_two v hv] at htower
  have hpos := Ideal.ramificationIdx_pos v.asIdeal ℤ
  omega

theorem q8QuadraticSourceCentral_mem_chosenDecomposition
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceCentral ∈
      absoluteValueDecompositionGroup S
        (chosenFinitePlaceExtension (L := K3) v).1 := by
  let w := chosenFinitePlaceExtension (L := K3) v
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v w
  letI := finitePlaceMulAction S K3
  rw [absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
    (K := S) (L := K3) v w]
  have hPtwo : (2 : 𝓞 K3) ∈ P.asIdeal := by
    have hPover : P.asIdeal.LiesOver v.asIdeal :=
      finitePlaceExtensionCentre_liesOver (K := S) (L := K3) v w
    change algebraMap (𝓞 S) (𝓞 K3) (2 : 𝓞 S) ∈ P.asIdeal
    rw [← Ideal.mem_comap]
    change (2 : 𝓞 S) ∈ P.asIdeal.under (𝓞 S)
    rw [← hPover.over]
    exact hv
  have hcRat : q8CAlgEquiv ∈ P.asIdeal.inertia Gal(K3/ℚ) := by
    have hc' := (q8Literal_two_inertia_eq_center P.asIdeal hPtwo).symm.le
      (Subgroup.mem_zpowers q8CAlgEquiv)
    exact hc'
  have hcSource : q8QuadraticSourceCentral ∈
      P.asIdeal.inertia Gal(K3/S) := by
    intro x
    have hx := hcRat x
    have hsmul : q8QuadraticSourceCentral • x = q8CAlgEquiv • x := by
      apply Subtype.ext
      exact DFunLike.congr_fun q8QuadraticSourceCentral_restrictScalars (x : K3)
    rw [hsmul]
    exact hx
  have hcSourceStab : q8QuadraticSourceCentral ∈
      MulAction.stabilizer Gal(K3/S) P.asIdeal :=
    Ideal.inertia_le_stabilizer P.asIdeal hcSource
  rw [MulAction.mem_stabilizer_iff] at hcSourceStab ⊢
  change finitePlaceEquiv S K3 q8QuadraticSourceCentral P = P
  apply HeightOneSpectrum.ext
  rw [finitePlaceEquiv_asIdeal]
  convert hcSourceStab using 1
  ext x
  rfl

abbrev q8ChosenGlobalValuationRing
    (v : HeightOneSpectrum (𝓞 S)) :=
  finitePlaceExtensionValuationSubring (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)

noncomputable def q8ChosenGlobalLocalizationEquiv
    (v : HeightOneSpectrum (𝓞 S)) :
    q8ChosenGlobalValuationRing v ≃+*
      Localization.AtPrime
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)).asIdeal :=
  (RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring
        (finitePlaceExtensionValuationSubring_eq_localization
          (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)))).trans
    (GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K3
      (finitePlaceExtensionCentre (K := S) (L := K3) v
        (chosenFinitePlaceExtension (L := K3) v))).toRingEquiv.symm

noncomputable def q8QuadraticSourceCentralChosenDecomposition
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup S
      (q8ChosenGlobalValuationRing v) :=
  let vK := NumberField.HeightOneSpectrum.adicAbv S v
  let w := chosenFinitePlaceExtension (L := K3) v
  let hw := finitePlaceExtension_nonarchimedean (K := S) (L := K3) v w
  HilbertRamification.localizationRamificationGroups_absoluteValueDecompositionGroupEquiv
    vK (RayClass.adicAbv_isNontrivial v) w hw
      ⟨q8QuadraticSourceCentral,
        q8QuadraticSourceCentral_mem_chosenDecomposition v hv⟩

noncomputable def q8PlaceLocalizationToTopField
    (P : HeightOneSpectrum (𝓞 K3)) :
    Localization.AtPrime P.asIdeal →+* K3 :=
  (HeightOneSpectrum.valuationSubringAtPrime K3 P).subtype.comp
    (GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K3
      P).toRingHom

theorem q8PlaceLocalizationToTopField_injective
    (P : HeightOneSpectrum (𝓞 K3)) :
    Function.Injective (q8PlaceLocalizationToTopField P) :=
  Subtype.coe_injective.comp
    (GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K3 P).injective

theorem q8LiteralCentralLocalEquiv_toTopField
    (P : HeightOneSpectrum (𝓞 K3)) [P.asIdeal.IsMaximal]
    (hPtwo : (2 : 𝓞 K3) ∈ P.asIdeal)
    (y : Localization.AtPrime P.asIdeal) :
    q8PlaceLocalizationToTopField P
        (q8LiteralCentralLocalEquiv P.asIdeal hPtwo y) =
      q8CAlgEquiv (q8PlaceLocalizationToTopField P y) := by
  let f : Localization.AtPrime P.asIdeal →+* K3 :=
    q8PlaceLocalizationToTopField P
  have hhom :
      f.comp (q8LiteralCentralLocalEquiv P.asIdeal hPtwo).toRingHom =
        q8CAlgEquiv.toRingHom.comp f := by
    apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply]
    change f (q8LiteralCentralLocalEquiv P.asIdeal hPtwo
      (algebraMap (𝓞 K3) (Localization.AtPrime P.asIdeal) x)) =
      q8CAlgEquiv
        (f (algebraMap (𝓞 K3) (Localization.AtPrime P.asIdeal) x))
    rw [q8LiteralCentralLocalEquiv_algebraMap]
    simp only [q8PlaceLocalizationToTopField,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      RingHom.coe_comp, ValuationSubring.coe_subtype, RingHom.coe_coe,
      Function.comp_apply, AlgEquiv.commutes, f]
    have hcoe (z : 𝓞 K3) :
        ((algebraMap (𝓞 K3)
          (HeightOneSpectrum.valuationSubringAtPrime K3 P) z :
            HeightOneSpectrum.valuationSubringAtPrime K3 P) : K3) =
          (z : K3) := by
      change (algebraMap
          (HeightOneSpectrum.valuationSubringAtPrime K3 P) K3)
            (algebraMap (𝓞 K3)
              (HeightOneSpectrum.valuationSubringAtPrime K3 P) z) =
        algebraMap (𝓞 K3) K3 z
      exact (IsScalarTower.algebraMap_apply (𝓞 K3)
        (HeightOneSpectrum.valuationSubringAtPrime K3 P) K3 z).symm
    rw [hcoe, hcoe]
    exact q8LiteralCentralIntegralEquiv_coe x
  exact DFunLike.congr_fun hhom y

theorem q8ChosenGlobalLocalizationEquiv_toTopField
    (v : HeightOneSpectrum (𝓞 S))
    (x : q8ChosenGlobalValuationRing v) :
    q8PlaceLocalizationToTopField
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v))
      (q8ChosenGlobalLocalizationEquiv v x) =
      (x : K3) := by
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  let e := GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K3 P
  let s : q8ChosenGlobalValuationRing v ≃+*
      HeightOneSpectrum.valuationSubringAtPrime K3 P :=
    RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring
        (finitePlaceExtensionValuationSubring_eq_localization
          (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)))
  change (HeightOneSpectrum.valuationSubringAtPrime K3 P).subtype
      (e (e.symm (s x))) = (x : K3)
  rw [e.apply_symm_apply]
  rfl

theorem q8QuadraticSourceCentralChosenDecomposition_smul_coe
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (x : q8ChosenGlobalValuationRing v) :
    (((q8QuadraticSourceCentralChosenDecomposition v hv) • x :
        q8ChosenGlobalValuationRing v) : K3) =
      q8CAlgEquiv (x : K3) := by
  change q8QuadraticSourceCentral (x : K3) =
    q8CAlgEquiv (x : K3)
  exact DFunLike.congr_fun q8QuadraticSourceCentral_restrictScalars
    (x : K3)

theorem q8ChosenGlobalLocalizationEquiv_intertwines_central
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (x : q8ChosenGlobalValuationRing v) :
    q8ChosenGlobalLocalizationEquiv v
        ((q8QuadraticSourceCentralChosenDecomposition v hv) • x) =
      q8LiteralCentralLocalEquiv
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)).asIdeal
        (q8FinitePlaceExtensionCentre_two_mem v hv)
        (q8ChosenGlobalLocalizationEquiv v x) := by
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  apply q8PlaceLocalizationToTopField_injective P
  rw [q8ChosenGlobalLocalizationEquiv_toTopField]
  rw [q8LiteralCentralLocalEquiv_toTopField]
  rw [q8ChosenGlobalLocalizationEquiv_toTopField]
  exact q8QuadraticSourceCentralChosenDecomposition_smul_coe v hv x

theorem q8QuadraticSourceCentralChosenDecomposition_displacement_mem_cube
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (x : q8ChosenGlobalValuationRing v) :
    (q8QuadraticSourceCentralChosenDecomposition v hv) • x - x ∈
      IsLocalRing.maximalIdeal (q8ChosenGlobalValuationRing v) ^ 3 := by
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  let E := q8ChosenGlobalLocalizationEquiv v
  letI : IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) P.ne_bot (Localization.AtPrime P.asIdeal)
  have hloc : E
      ((q8QuadraticSourceCentralChosenDecomposition v hv) • x - x) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ 3 := by
    rw [map_sub, q8ChosenGlobalLocalizationEquiv_intertwines_central]
    rw [GaloisForLFunctions.HTGeometry.mem_maximalIdeal_pow_iff_le_addVal]
    exact q8LiteralCentralLocalEquiv_sub_addVal_ge_three P.asIdeal
      (q8FinitePlaceExtensionCentre_two_mem v hv) (E x)
  exact (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff E 3 _).1 hloc

noncomputable def q8QuadraticSourceChosenTopRadical
    (v : HeightOneSpectrum (𝓞 S)) :
    q8ChosenGlobalValuationRing v :=
  (q8ChosenGlobalLocalizationEquiv v).symm
    (algebraMap (𝓞 K3)
      (Localization.AtPrime
        (finitePlaceExtensionCentre (K := S) (L := K3) v
          (chosenFinitePlaceExtension (L := K3) v)).asIdeal)
      q8LiteralTwoAdicZ)

@[simp] theorem q8ChosenGlobalLocalizationEquiv_chosenTopRadical
    (v : HeightOneSpectrum (𝓞 S)) :
    q8ChosenGlobalLocalizationEquiv v
        (q8QuadraticSourceChosenTopRadical v) =
      algebraMap (𝓞 K3)
        (Localization.AtPrime
          (finitePlaceExtensionCentre (K := S) (L := K3) v
            (chosenFinitePlaceExtension (L := K3) v)).asIdeal)
        q8LiteralTwoAdicZ := by
  exact (q8ChosenGlobalLocalizationEquiv v).apply_symm_apply _

theorem q8QuadraticSourceCentralChosenDecomposition_displacement_not_mem_four
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    (q8QuadraticSourceCentralChosenDecomposition v hv) •
          q8QuadraticSourceChosenTopRadical v -
        q8QuadraticSourceChosenTopRadical v ∉
      IsLocalRing.maximalIdeal (q8ChosenGlobalValuationRing v) ^ 4 := by
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
  let E := q8ChosenGlobalLocalizationEquiv v
  letI : IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) P.ne_bot (Localization.AtPrime P.asIdeal)
  intro hdeep
  have hloc : E
      ((q8QuadraticSourceCentralChosenDecomposition v hv) •
          q8QuadraticSourceChosenTopRadical v -
        q8QuadraticSourceChosenTopRadical v) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ 4 :=
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff E 4 _).2 hdeep
  rw [map_sub, q8ChosenGlobalLocalizationEquiv_intertwines_central,
    q8ChosenGlobalLocalizationEquiv_chosenTopRadical] at hloc
  rw [GaloisForLFunctions.HTGeometry.mem_maximalIdeal_pow_iff_le_addVal] at hloc
  rw [q8LiteralCentralLocalEquiv_algebraMap] at hloc
  have heq : q8LiteralCentralIntegralEquiv q8LiteralTwoAdicZ =
      q8CAlgEquiv • q8LiteralTwoAdicZ := rfl
  rw [heq, ← map_sub] at hloc
  rw [q8Literal_two_local_addVal_centralDisplacement_eq_three
    P.asIdeal (q8FinitePlaceExtensionCentre_two_mem v hv)] at hloc
  norm_num at hloc

/-- Local completed image of the actual central source involution. -/
noncomputable def q8QuadraticSourceCentralChosenLocalEquiv
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := S) v]
      ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v :=
  HilbertRamification.localizationRamificationGroups_valuationDecompositionGroupEquiv
    (NumberField.HeightOneSpectrum.adicAbv S v)
    (RayClass.adicAbv_isNontrivial v)
    (chosenFinitePlaceExtension (L := K3) v)
    (finitePlaceExtension_nonarchimedean (K := S) (L := K3) v
      (chosenFinitePlaceExtension (L := K3) v))
    (q8QuadraticSourceCentralChosenDecomposition v hv)

/-- Completed image of the source top radical witnessing exact central displacement depth. -/
noncomputable def q8QuadraticSourceChosenCompletedTopRadical
    (v : HeightOneSpectrum (𝓞 S)) :
    HilbertRamification.chosenLocalIntegerRing (K := S) (L := K3) v :=
  HilbertRamification.chosenGlobalToLocalIntegerRing
    (K := S) (L := K3) v (q8QuadraticSourceChosenTopRadical v)

set_option maxHeartbeats 1200000 in
theorem q8QuadraticSourceCentralChosenCompletion_displacement_mem_cube
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (z : 𝒪[ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v]) :
    HilbertRamification.chosenLocalIntegerRingAut
        (K := S) (L := K3) v
        (q8QuadraticSourceCentralChosenLocalEquiv v hv) z - z ∈
      IsLocalRing.maximalIdeal
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v] ^ (2 + 1) := by
  simpa only [q8QuadraticSourceCentralChosenLocalEquiv] using
    HilbertRamification.chosenDecompositionDisplacement_mem_local_of_global
      (K := S) (L := K3) v 3
        (q8QuadraticSourceCentralChosenDecomposition v hv)
        (q8QuadraticSourceCentralChosenDecomposition_displacement_mem_cube v hv) z

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
/-- The canonical source embedding preserves the exact first excluded depth of the central
radical displacement. -/
theorem q8QuadraticSourceCentralChosenCompletion_mappedDisplacement_not_mem_four
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    HilbertRamification.chosenGlobalToLocalIntegerRing
          (K := S) (L := K3) v
          ((q8QuadraticSourceCentralChosenDecomposition v hv) •
              q8QuadraticSourceChosenTopRadical v -
            q8QuadraticSourceChosenTopRadical v) ∉
      IsLocalRing.maximalIdeal
        (HilbertRamification.chosenLocalIntegerRing (K := S) (L := K3) v) ^ (3 + 1) := by
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
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
  intro hlocal
  have hglobal :=
    (HilbertRamification.chosenGlobalToLocalIntegerRing_mem_maximalIdeal_pow_iff
      (K := S) (L := K3) v 4
      ((q8QuadraticSourceCentralChosenDecomposition v hv) •
          q8QuadraticSourceChosenTopRadical v -
        q8QuadraticSourceChosenTopRadical v)).1 hlocal
  exact q8QuadraticSourceCentralChosenDecomposition_displacement_not_mem_four
    v hv hglobal

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 2000000 in
/-- Membership of the completed central displacement in the fourth maximal-ideal power is
impossible.  This implication form avoids normalizing a large negated membership proposition at
downstream exact-break call sites. -/
theorem q8QuadraticSourceCentralChosenCompletion_displacement_mem_four_false
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (hlocal : HilbertRamification.chosenLocalIntegerRingAut
          (K := S) (L := K3) v
          (q8QuadraticSourceCentralChosenLocalEquiv v hv)
          (q8QuadraticSourceChosenCompletedTopRadical v) -
        q8QuadraticSourceChosenCompletedTopRadical v ∈
      IsLocalRing.maximalIdeal
        (HilbertRamification.chosenLocalIntegerRing (K := S) (L := K3) v) ^ (3 + 1)) : False := by
  let sigma := q8QuadraticSourceCentralChosenDecomposition v hv
  let x := q8QuadraticSourceChosenTopRadical v
  have hcomm :=
    HilbertRamification.chosenLocalIntegerRingAut_chosenGlobalToLocalIntegerRing_sub
      (K := S) (L := K3) v sigma x
  have hmapped :
      HilbertRamification.chosenGlobalToLocalIntegerRing
          (K := S) (L := K3) v (sigma • x - x) ∈
        IsLocalRing.maximalIdeal
          (HilbertRamification.chosenLocalIntegerRing (K := S) (L := K3) v) ^ (3 + 1) := by
    exact (congrArg (fun y => y ∈ IsLocalRing.maximalIdeal
      (HilbertRamification.chosenLocalIntegerRing (K := S) (L := K3) v) ^ (3 + 1)) hcomm).mp hlocal
  exact q8QuadraticSourceCentralChosenCompletion_mappedDisplacement_not_mem_four
    v hv hmapped

/-- The completed central action has exact lower displacement depth three on the embedded
source radical.  Completion therefore preserves the first excluded depth, rather than only the
forward cube congruence. -/
theorem q8QuadraticSourceCentralChosenCompletion_displacement_not_mem_four
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    HilbertRamification.chosenLocalIntegerRingAut
          (K := S) (L := K3) v
          (q8QuadraticSourceCentralChosenLocalEquiv v hv)
          (q8QuadraticSourceChosenCompletedTopRadical v) -
        q8QuadraticSourceChosenCompletedTopRadical v ∉
      IsLocalRing.maximalIdeal
        (HilbertRamification.chosenLocalIntegerRing (K := S) (L := K3) v) ^ (3 + 1) :=
  fun hlocal =>
    q8QuadraticSourceCentralChosenCompletion_displacement_mem_four_false v hv hlocal

set_option maxHeartbeats 1200000 in
/-- The completed central source involution survives in the actual local lower group through
level two.  This is the completed-group form needed by filtered local reciprocity. -/
theorem q8QuadraticSourceCentralChosenLocalEquiv_mem_actualLower_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceCentralChosenLocalEquiv v hv ∈
      HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v 2 := by
  apply (HilbertRamification.mem_chosenActualLocalLowerRamificationGroup_iff
    (K := S) (L := K3) v 2 (q8QuadraticSourceCentralChosenLocalEquiv v hv)).2
  intro z
  have h := q8QuadraticSourceCentralChosenCompletion_displacement_mem_cube v hv z
  rw [GaloisForLFunctions.HTGeometry.mem_maximalIdeal_pow_iff_le_addVal] at h ⊢
  exact h

set_option maxHeartbeats 2000000 in
/-- Membership of the completed central source involution in actual lower level three is
impossible.  Keeping membership explicit avoids normalizing the large negated subgroup
proposition before the intrinsic displacement criterion is applied. -/
theorem q8QuadraticSourceCentralChosenLocalEquiv_mem_actualLower_three_false
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (hmem : q8QuadraticSourceCentralChosenLocalEquiv v hv ∈
      HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v 3) : False := by
  have hdeep :=
    (HilbertRamification.mem_chosenActualLocalLowerRamificationGroup_iff
      (K := S) (L := K3) v 3
        (q8QuadraticSourceCentralChosenLocalEquiv v hv)).1 hmem
      (q8QuadraticSourceChosenCompletedTopRadical v)
  let sigma := q8QuadraticSourceCentralChosenDecomposition v hv
  let x := q8QuadraticSourceChosenTopRadical v
  have hcomm :=
    HilbertRamification.chosenLocalIntegerRingAut_chosenGlobalToLocalIntegerRing_sub
      (K := S) (L := K3) v sigma x
  have hmapped := (congrArg (fun y => y ∈ IsLocalRing.maximalIdeal
    (HilbertRamification.chosenLocalIntegerRing (K := S) (L := K3) v) ^ (3 + 1)) hcomm).mp hdeep
  let P := finitePlaceExtensionCentre (K := S) (L := K3) v
    (chosenFinitePlaceExtension (L := K3) v)
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
  dsimp only [sigma, x] at hmapped
  have hglobal :=
    (HilbertRamification.chosenGlobalToLocalIntegerRing_mem_maximalIdeal_pow_iff
      (K := S) (L := K3) v 4
      ((q8QuadraticSourceCentralChosenDecomposition v hv) •
          q8QuadraticSourceChosenTopRadical v -
        q8QuadraticSourceChosenTopRadical v)).1 hmapped
  exact q8QuadraticSourceCentralChosenDecomposition_displacement_not_mem_four
    v hv hglobal

/-- Exact end of the completed central lower break: the central source involution is absent from
actual local lower level three. -/
theorem q8QuadraticSourceCentralChosenLocalEquiv_not_mem_actualLower_three
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceCentralChosenLocalEquiv v hv ∉
      HilbertRamification.chosenActualLocalLowerRamificationGroup
        (K := S) (L := K3) v 3 :=
  fun hmem =>
    q8QuadraticSourceCentralChosenLocalEquiv_mem_actualLower_three_false v hv hmem

/-- CFT local lower level two contains the actual completed central source involution. -/
theorem q8QuadraticSourceCentralChosenLocalEquiv_mem_localLower_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceCentralChosenLocalEquiv v hv ∈
      RamificationTheory.LocalField.localLowerRamificationGroup
        (ChosenFinitePlaceBaseCompletion (K := S) v)
        (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (2 : ℝ) := by
  have h := q8QuadraticSourceCentralChosenLocalEquiv_mem_actualLower_two v hv
  rw [HilbertRamification.chosenActualLocalLowerRamificationGroup_eq_localLower
    (K := S) (L := K3) v 2] at h
  exact h

/-- CFT local lower level three excludes the actual completed central source involution. -/
theorem q8QuadraticSourceCentralChosenLocalEquiv_not_mem_localLower_three
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceCentralChosenLocalEquiv v hv ∉
      RamificationTheory.LocalField.localLowerRamificationGroup
        (ChosenFinitePlaceBaseCompletion (K := S) v)
        (ChosenFinitePlaceLocalizedCompletion (K := S) (L := K3) v) (3 : ℝ) := by
  have h := q8QuadraticSourceCentralChosenLocalEquiv_not_mem_actualLower_three v hv
  rw [HilbertRamification.chosenActualLocalLowerRamificationGroup_eq_localLower
    (K := S) (L := K3) v 3] at h
  exact h

end

end RHTower
