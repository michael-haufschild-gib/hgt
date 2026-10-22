import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicMonogenic
import GaloisForLFunctions.HTGeometry.LowerRamificationArtinConductor

namespace RHTower

open scoped NumberField Pointwise
open IsDiscreteValuationRing
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField
local notation "G3" => K3 ≃ₐ[ℚ] K3

attribute [local instance]
  deningerQ8MaxAbAlgebra
  q8InertiaCharZeroK2 q8InertiaCharZeroK3
  q8InertiaFiniteDimensionalRatK1 q8InertiaFiniteDimensionalK1K2
  q8InertiaFiniteDimensionalRatK2 q8InertiaFiniteDimensionalK2K3
  q8InertiaFiniteDimensionalRatK3 q8InertiaNumberFieldK2 q8InertiaNumberFieldK3
  q8InertiaIsGalois

noncomputable def q8LiteralCentralIntegralEquiv : 𝓞 K3 ≃+* 𝓞 K3 :=
  MulSemiringAction.toRingEquiv G3 (𝓞 K3) q8CAlgEquiv

@[simp] theorem q8LiteralCentralIntegralEquiv_coe (x : 𝓞 K3) :
    ((q8LiteralCentralIntegralEquiv x : 𝓞 K3) : K3) = q8CAlgEquiv (x : K3) := rfl

theorem q8LiteralCentralIntegralEquiv_map_primeCompl
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    P.primeCompl.map q8LiteralCentralIntegralEquiv.toMonoidHom = P.primeCompl := by
  have hc : q8CAlgEquiv ∈ P.inertia G3 := by
    have hc' := (q8Literal_two_inertia_eq_center P hPtwo).symm.le
      (Subgroup.mem_zpowers q8CAlgEquiv)
    change q8CAlgEquiv ∈ P.inertia G3 at hc'
    exact hc'
  let tau := q8LiteralCentralIntegralEquiv
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change tau x ∉ P
    intro htx
    apply hx
    have hdiff : tau x - x ∈ P := hc x
    simpa using P.sub_mem htx hdiff
  · intro y hy
    refine ⟨tau.symm y, ?_, tau.apply_symm_apply y⟩
    change tau.symm y ∉ P
    intro hpre
    apply hy
    have hdiff : tau (tau.symm y) - tau.symm y ∈ P := hc (tau.symm y)
    simpa using P.add_mem hdiff hpre

noncomputable def q8LiteralCentralLocalEquiv
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    Localization.AtPrime P ≃+* Localization.AtPrime P :=
  IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime P) (Localization.AtPrime P)
    q8LiteralCentralIntegralEquiv
    (q8LiteralCentralIntegralEquiv_map_primeCompl P hPtwo)

@[simp] theorem q8LiteralCentralLocalEquiv_algebraMap
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (x : 𝓞 K3) :
    q8LiteralCentralLocalEquiv P hPtwo
        (algebraMap (𝓞 K3) (Localization.AtPrime P) x) =
      algebraMap (𝓞 K3) (Localization.AtPrime P)
        (q8LiteralCentralIntegralEquiv x) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (q8LiteralCentralIntegralEquiv_map_primeCompl P hPtwo) x

@[simp] theorem q8LiteralCentralIntegralEquiv_algebraMap_biquad
    (x : 𝓞 K2) :
    q8LiteralCentralIntegralEquiv
        (algebraMap (𝓞 K2) (𝓞 K3) x) =
      algebraMap (𝓞 K2) (𝓞 K3) x := by
  apply Subtype.ext
  change q8CAlgEquiv (algebraMap K2 K3 (x : K2)) =
    algebraMap K2 K3 (x : K2)
  rw [q8CAlgEquiv_apply]
  exact q8C_of (x : K2)

@[simp] theorem q8LiteralCentralIntegralEquiv_topRadical :
    q8LiteralCentralIntegralEquiv q8LiteralTwoAdicZ = -q8LiteralTwoAdicZ := by
  have h := q8Literal_centralInvolution_sub_topRadical
  change q8LiteralCentralIntegralEquiv q8LiteralTwoAdicZ - q8LiteralTwoAdicZ =
    -2 * q8LiteralTwoAdicZ at h
  linear_combination h

@[simp] theorem q8LiteralCentralLocalEquiv_topRadical
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    q8LiteralCentralLocalEquiv P hPtwo
        (algebraMap (𝓞 K3) (Localization.AtPrime P) q8LiteralTwoAdicZ) =
      -algebraMap (𝓞 K3) (Localization.AtPrime P) q8LiteralTwoAdicZ := by
  rw [q8LiteralCentralLocalEquiv_algebraMap,
    q8LiteralCentralIntegralEquiv_topRadical, map_neg]

@[simp] theorem q8LiteralCentralLocalEquiv_algebraMap_biquadLocalization
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
    let A := Localization.AtPrime Q
    let B := Localization.AtPrime P
    letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
    ∀ a : A, q8LiteralCentralLocalEquiv P hPtwo (algebraMap A B a) =
      algebraMap A B a := by
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime P
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
  let e := q8LiteralCentralLocalEquiv P hPtwo
  have hhom : e.toRingHom.comp (algebraMap A B) = algebraMap A B := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K2) A B]
    rw [IsScalarTower.algebraMap_apply (𝓞 K2) (𝓞 K3) B]
    change q8LiteralCentralLocalEquiv P hPtwo
        (algebraMap (𝓞 K3) B (algebraMap (𝓞 K2) (𝓞 K3) x)) = _
    rw [q8LiteralCentralLocalEquiv_algebraMap,
      q8LiteralCentralIntegralEquiv_algebraMap_biquad]
  change ∀ a : A, e (algebraMap A B a) = algebraMap A B a
  exact fun a => RingHom.congr_fun hhom a

theorem q8LiteralCentralLocalEquiv_sub_eq
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
    let A := Localization.AtPrime Q
    let B := Localization.AtPrime P
    letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
    letI : Module.Finite A B := Localization.finite_of_primesOver_eq_singleton
      (q8Literal_two_relative_primesOver_eq_singleton P hPtwo)
    ∀ y : B, ∃ a₁ : A,
      q8LiteralCentralLocalEquiv P hPtwo y - y =
        -2 * algebraMap A B a₁ *
          algebraMap (𝓞 K3) B q8LiteralTwoAdicZ := by
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime P
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
  letI : Module.Finite A B := Localization.finite_of_primesOver_eq_singleton
    (q8Literal_two_relative_primesOver_eq_singleton P hPtwo)
  change ∀ y : B, ∃ a₁ : A, _
  intro y
  obtain ⟨a₀, a₁, hy⟩ := q8Literal_two_local_exists_linearCoordinates P hPtwo y
  refine ⟨a₁, ?_⟩
  rw [hy, map_add, map_mul,
    q8LiteralCentralLocalEquiv_algebraMap_biquadLocalization P hPtwo,
    q8LiteralCentralLocalEquiv_algebraMap_biquadLocalization P hPtwo,
    q8LiteralCentralLocalEquiv_topRadical P hPtwo]
  ring

theorem q8LiteralCentralLocalEquiv_sub_addVal_ge_three
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
    let A := Localization.AtPrime Q
    let B := Localization.AtPrime P
    letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
    letI : IsDiscreteValuationRing B :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (𝓞 K3) (show P ≠ ⊥ from by
          intro hP
          rw [hP, Ideal.mem_bot] at hPtwo
          norm_num at hPtwo) B
    ∀ y : B, (3 : ℕ∞) ≤
      addVal B (q8LiteralCentralLocalEquiv P hPtwo y - y) := by
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime P
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
  letI : Module.Finite A B := Localization.finite_of_primesOver_eq_singleton
    (q8Literal_two_relative_primesOver_eq_singleton P hPtwo)
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) B
  letI : CharZero B := charZero_of_injective_algebraMap
    (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)
  change ∀ y : B, (3 : ℕ∞) ≤ addVal B (q8LiteralCentralLocalEquiv P hPtwo y - y)
  intro y
  obtain ⟨a₁, hy⟩ := q8LiteralCentralLocalEquiv_sub_eq P hPtwo y
  have htwo : addVal B (2 : B) = 2 := q8Literal_two_local_addVal_two_eq_two P hPtwo
  have hnegTwo : addVal B (-2 : B) = 2 := by
    rw [show (-2 : B) = (-1) * 2 by ring, addVal_mul, htwo]
    simp
  have hz : addVal B (algebraMap (𝓞 K3) B q8LiteralTwoAdicZ) = 1 :=
    q8Literal_two_local_addVal_topRadical_eq_one P hPtwo
  rw [hy, addVal_mul, addVal_mul, hnegTwo, hz]
  calc
    (3 : ℕ∞) = 2 + 0 + 1 := by norm_num
    _ ≤ 2 + addVal B (algebraMap A B a₁) + 1 := by
      gcongr
      exact bot_le

/-- The literal central involution survives through lower level two at every prime above two. -/
theorem q8Literal_centralInvolution_mem_lowerRamificationGroup_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    q8CAlgEquiv ∈
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 2 := by
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) (Localization.AtPrime P)
  change ∀ x : 𝓞 K3,
    algebraMap (𝓞 K3) (Localization.AtPrime P) (q8CAlgEquiv • x - x) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ 3
  intro x
  rw [GaloisForLFunctions.HTGeometry.mem_maximalIdeal_pow_iff_le_addVal]
  have h := q8LiteralCentralLocalEquiv_sub_addVal_ge_three P hPtwo
    (algebraMap (𝓞 K3) (Localization.AtPrime P) x)
  rw [q8LiteralCentralLocalEquiv_algebraMap] at h
  have heq : q8LiteralCentralIntegralEquiv x = q8CAlgEquiv • x := rfl
  rw [heq] at h
  rw [map_sub]
  convert h using 1
  norm_num

/-- The same involution drops out exactly after lower level two. -/
theorem q8Literal_centralInvolution_not_mem_lowerRamificationGroup_three
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    q8CAlgEquiv ∉
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 3 := by
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) (Localization.AtPrime P)
  intro hc
  change ∀ x : 𝓞 K3,
    algebraMap (𝓞 K3) (Localization.AtPrime P) (q8CAlgEquiv • x - x) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ 4 at hc
  have hz := hc q8LiteralTwoAdicZ
  rw [GaloisForLFunctions.HTGeometry.mem_maximalIdeal_pow_iff_le_addVal] at hz
  have hexact := q8Literal_two_local_addVal_centralDisplacement_eq_three P hPtwo
  rw [hexact] at hz
  norm_num at hz

/-- Lower level zero is the already-computed central inertia subgroup. -/
theorem q8Literal_two_lowerRamificationGroup_zero
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 0 = deningerQ8ActualCentralSubgroup := by
  rw [GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_eq_lowerRamificationGroup]
  unfold GaloisForLFunctions.HTGeometry.Ideal.lowerRamificationGroup
  simp only [zero_add, pow_one]
  change P.inertia G3 = deningerQ8ActualCentralSubgroup
  exact q8Literal_two_inertia_eq_center P hPtwo

/-- Wild persistence through level two: the whole order-two inertia group survives. -/
theorem q8Literal_two_lowerRamificationGroup_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 2 = deningerQ8ActualCentralSubgroup := by
  apply le_antisymm
  · have hle :=
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_antitone
        (G := G3) P (show 0 ≤ 2 by omega)
    change GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 2 ≤
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 0 at hle
    rw [q8Literal_two_lowerRamificationGroup_zero P hPtwo] at hle
    exact hle
  · exact Subgroup.zpowers_le.mpr
      (q8Literal_centralInvolution_mem_lowerRamificationGroup_two P hPtwo)

/-- The intermediate wild level is forced by antitonicity between equal endpoints. -/
theorem q8Literal_two_lowerRamificationGroup_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 1 = deningerQ8ActualCentralSubgroup := by
  apply le_antisymm
  · have hle :=
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_antitone
        (G := G3) P (show 0 ≤ 1 by omega)
    change GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 1 ≤
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 0 at hle
    rw [q8Literal_two_lowerRamificationGroup_zero P hPtwo] at hle
    exact hle
  · rw [← q8Literal_two_lowerRamificationGroup_two P hPtwo]
    exact GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_antitone
      (G := G3) P (by omega)

/-- Exact end of the wild break: lower level three is trivial. -/
theorem q8Literal_two_lowerRamificationGroup_three
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 3 = ⊥ := by
  let H := GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
    (G := G3) P 3
  let C := GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
    (G := G3) P 0
  have hHle :=
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_antitone
      (G := G3) P (show 0 ≤ 3 by omega)
  change H ≤ C at hHle
  have hcnot : q8CAlgEquiv ∉ H :=
    q8Literal_centralInvolution_not_mem_lowerRamificationGroup_three P hPtwo
  have hCcard : Nat.card C = 2 := by
    change Nat.card
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 0) = 2
    rw [GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_eq_lowerRamificationGroup]
    unfold GaloisForLFunctions.HTGeometry.Ideal.lowerRamificationGroup
    simp only [zero_add, pow_one]
    change Nat.card (P.inertia G3) = 2
    exact q8Literal_two_inertia_natCard_eq_two P hPtwo
  haveI : Fact (Nat.card C).Prime := ⟨by
    rw [hCcard]
    norm_num⟩
  let HC : Subgroup C := H.comap C.subtype
  have hHCbot : HC = ⊥ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card HC with hbot | htop
    · exact hbot
    · exfalso
      apply hcnot
      have h20 :=
        GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_antitone
          (G := G3) P (show 0 ≤ 2 by omega)
      change GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
          (G := G3) P 2 ≤ C at h20
      have hcC : q8CAlgEquiv ∈ C :=
        h20 (q8Literal_centralInvolution_mem_lowerRamificationGroup_two P hPtwo)
      have hcHC : (⟨q8CAlgEquiv, hcC⟩ : C) ∈ HC := by
        rw [htop]
        exact Subgroup.mem_top _
      exact hcHC
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_bot]
    have hgC : g ∈ C := hHle hg
    have hgHC : (⟨g, hgC⟩ : C) ∈ HC := hg
    rw [hHCbot] at hgHC
    simpa using hgHC
  · exact bot_le

/-- Every later lower ramification group is trivial. -/
theorem q8Literal_two_lowerRamificationGroup_eq_bot_of_three_le
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : 3 ≤ n) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n = ⊥ := by
  apply le_antisymm
  · have hle :=
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_antitone
        (G := G3) P hn
    change GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n ≤
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 3 at hle
    rw [q8Literal_two_lowerRamificationGroup_three P hPtwo] at hle
    exact hle
  · exact bot_le

/-- Complete lower-numbering profile of the literal two-adic Q8 extension. -/
theorem q8Literal_two_lowerRamificationGroup_profile
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) :
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n =
      if n ≤ 2 then deningerQ8ActualCentralSubgroup else ⊥ := by
  by_cases hn : n ≤ 2
  · rw [if_pos hn]
    interval_cases n
    · exact q8Literal_two_lowerRamificationGroup_zero P hPtwo
    · exact q8Literal_two_lowerRamificationGroup_one P hPtwo
    · exact q8Literal_two_lowerRamificationGroup_two P hPtwo
  · rw [if_neg hn]
    exact q8Literal_two_lowerRamificationGroup_eq_bot_of_three_le
      P hPtwo n (by omega)

/-- Every nontrivial lower level has zero fixed space on the literal Artin carrier. -/
theorem q8Literal_two_artin_lower_invariants_eq_bot_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    Representation.invariants
      ((deningerQ8ArtinRepresentation
        deningerQ8RootNumberNegOne_galoisEquivQ8).comp
          (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
            (G := G3) P n).subtype) = ⊥ := by
  have hnGroup := q8Literal_two_lowerRamificationGroup_profile P hPtwo n
  rw [if_pos hn] at hnGroup
  rw [hnGroup, ← q8Literal_two_inertia_eq_center P hPtwo]
  exact q8Literal_two_artin_fullInertia_invariants_eq_bot P hPtwo

/-- Each occupied lower level contributes full carrier codimension two. -/
theorem q8Literal_two_artin_lowerArtinCodimension_eq_two_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinCodimension
      (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n) = 2 := by
  let rho := deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8
  let H := GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
    (G := G3) P n
  change GaloisForLFunctions.HTGeometry.Representation.lowerArtinCodimension
    rho H = 2
  have hinv : Representation.invariants (rho.comp H.subtype) = ⊥ := by
    simpa only [rho, H] using
      q8Literal_two_artin_lower_invariants_eq_bot_of_le_two P hPtwo n hn
  have hrank : Module.finrank ℂ
      (Representation.invariants (rho.comp H.subtype)) = 0 := by
    rw [hinv]
    simp
  unfold GaloisForLFunctions.HTGeometry.Representation.lowerArtinCodimension
  rw [hrank, deningerQ8ArtinRepresentation_finrank]

/-- Every occupied lower level has order two. -/
theorem q8Literal_two_lowerRamificationGroup_natCard_eq_two_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    Nat.card
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n) = 2 := by
  have hnGroup := q8Literal_two_lowerRamificationGroup_profile P hPtwo n
  rw [if_pos hn] at hnGroup
  have hzero := q8Literal_two_lowerRamificationGroup_zero P hPtwo
  have hnZero :
      GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
          (G := G3) P n =
        GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
          (G := G3) P 0 := hnGroup.trans hzero.symm
  rw [hnZero,
    GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup_eq_lowerRamificationGroup]
  unfold GaloisForLFunctions.HTGeometry.Ideal.lowerRamificationGroup
  simp only [zero_add, pow_one]
  change Nat.card (P.inertia G3) = 2
  exact q8Literal_two_inertia_natCard_eq_two P hPtwo

/-- Every occupied lower level contributes exactly two to the Artin conductor. -/
theorem q8Literal_two_artin_lowerArtinTerm_eq_two_of_le_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : n ≤ 2) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
      (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 0)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n) = 2 := by
  let rho := deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8
  let Gzero := GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
    (G := G3) P 0
  let H := GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
    (G := G3) P n
  change GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
    rho Gzero H = 2
  have hcardH : Nat.card H = 2 := by
    simpa only [H] using
      q8Literal_two_lowerRamificationGroup_natCard_eq_two_of_le_two P hPtwo n hn
  have hcardZero : Nat.card Gzero = 2 := by
    simpa only [Gzero] using
      q8Literal_two_lowerRamificationGroup_natCard_eq_two_of_le_two
        P hPtwo 0 (by omega)
  have hcodim :
      GaloisForLFunctions.HTGeometry.Representation.lowerArtinCodimension rho H = 2 := by
    simpa only [rho, H] using
      q8Literal_two_artin_lowerArtinCodimension_eq_two_of_le_two P hPtwo n hn
  unfold GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
  rw [hcardH, hcardZero, hcodim]
  norm_num

/-- Every post-break level contributes zero to the Artin conductor. -/
theorem q8Literal_two_artin_lowerArtinTerm_eq_zero_of_three_le
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) (hn : 3 ≤ n) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
      (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 0)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n) = 0 := by
  rw [q8Literal_two_lowerRamificationGroup_eq_bot_of_three_le P hPtwo n hn]
  exact GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm_bot _ _

/-- Exact term profile: `2, 2, 2, 0, 0, ...`. -/
theorem q8Literal_two_artin_lowerArtinTerm_profile
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (n : ℕ) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinTerm
      (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P 0)
      (GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n) = if n ≤ 2 then 2 else 0 := by
  by_cases hn : n ≤ 2
  · rw [if_pos hn]
    exact q8Literal_two_artin_lowerArtinTerm_eq_two_of_le_two P hPtwo n hn
  · rw [if_neg hn]
    exact q8Literal_two_artin_lowerArtinTerm_eq_zero_of_three_le
      P hPtwo n (by omega)

/-- The literal two-adic Artin conductor is exactly six. -/
theorem q8Literal_two_artin_lowerArtinConductor_eq_six
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    GaloisForLFunctions.HTGeometry.Representation.lowerArtinConductorUpTo
      (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8)
      (fun n => GaloisForLFunctions.HTGeometry.Ideal.localizedLowerRamificationGroup
        (G := G3) P n) 4 = 6 := by
  unfold GaloisForLFunctions.HTGeometry.Representation.lowerArtinConductorUpTo
  norm_num [Finset.sum_range_succ,
    q8Literal_two_artin_lowerArtinTerm_profile P hPtwo]

end
end RHTower
