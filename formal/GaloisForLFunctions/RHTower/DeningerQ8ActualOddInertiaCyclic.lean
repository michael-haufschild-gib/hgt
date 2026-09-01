import GaloisForLFunctions.RHTower.DeningerQ8ActualOddInertia
import GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicInertia
import GaloisForLFunctions.HTGeometry.TameInertiaCyclic

/-!
# Exact odd inertia in the actual quaternion extension

At every top prime over `5` or `41`, inertia is cyclic of order four. The proof
uses tame inertia in odd residue characteristic, noncentrality forced by the
maximal abelian square-root subfield, and the subgroup lattice of `Q₈`.
-/

namespace RHTower

open scoped NumberField Pointwise
open GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8OddCyclicCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance q8OddCyclicFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8OddCyclicFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8OddCyclicFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8OddCyclicFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8OddCyclicFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8OddCyclicNumberFieldK3 : NumberField K3 := NumberField.mk
noncomputable local instance q8OddCyclicIsGaloisRatK3 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

theorem q8Actual_odd_inertia_isCyclic
    (p : ℤ) (hp : Prime p) (htwo : (2 : ℤ) ∉ Ideal.span {p})
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {p})) :
    IsCyclic (P.inertia Gal(K3/ℚ)) := by
  have hPp : algebraMap ℤ (𝓞 K3) p ∈ P :=
    (Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) hp).mp hPover
  have hPne : P ≠ ⊥ := by
    intro hP
    rw [hP, Ideal.mem_bot] at hPp
    have hcast : (p : 𝓞 K3) = ((0 : ℤ) : 𝓞 K3) := by simpa using hPp
    exact hp.ne_zero (Int.cast_injective hcast)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K3) :=
    ⟨P, (inferInstance : P.IsPrime), hPne⟩
  let W : ValuationSubring K3 :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K3 v
  letI : IsLocalization P.primeCompl W :=
    IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime
      v
  letI : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) hPne W
  have hW : W ≠ ⊤ := ValuationSubring.ne_top_of_isDiscreteValuationRing W
  have hSW : ∀ s : 𝓞 K3, algebraMap (𝓞 K3) K3 s ∈ W := by
    intro s
    exact (algebraMap (𝓞 K3) W s).property
  have hAW : ∀ a : ℤ, algebraMap ℤ K3 a ∈ W := by
    intro a
    have ha := hSW (algebraMap ℤ (𝓞 K3) a)
    simpa only [IsScalarTower.algebraMap_apply ℤ (𝓞 K3) K3] using ha
  have hcent : ∀ a : ℤ,
      (¬ IsUnit (⟨algebraMap ℤ K3 a, hAW a⟩ : W)) ↔ a ∈ Ideal.span {p} := by
    intro a
    have heq : (⟨algebraMap ℤ K3 a, hAW a⟩ : W) =
        algebraMap (𝓞 K3) W (algebraMap ℤ (𝓞 K3) a) := by
      apply Subtype.ext
      exact (IsScalarTower.algebraMap_apply ℤ (𝓞 K3) K3 a).symm
    rw [heq, IsLocalization.AtPrime.isUnit_to_map_iff W P]
    change (¬ algebraMap ℤ (𝓞 K3) a ∉ P) ↔ a ∈ Ideal.span {p}
    rw [not_not]
    change a ∈ P.comap (algebraMap ℤ (𝓞 K3)) ↔ a ∈ Ideal.span {p}
    have hover : Ideal.span {p} = P.comap (algebraMap ℤ (𝓞 K3)) := hPover.over
    rw [← hover]
  have hact : ∀ (g : Gal(K3/ℚ)) (s : 𝓞 K3),
      algebraMap (𝓞 K3) K3 (g • s) = g • algebraMap (𝓞 K3) K3 s := by
    intro g s
    rfl
  have hcenterPrime : ValuationInertia.centerPrime W hSW = P := by
    apply Ideal.ext
    intro s
    change ValuationInertia.toValuationSubring W hSW s ∈
        IsLocalRing.maximalIdeal W ↔ s ∈ P
    have heq : ValuationInertia.toValuationSubring W hSW s =
        algebraMap (𝓞 K3) W s := Subtype.ext rfl
    rw [heq, IsLocalization.AtPrime.to_map_mem_maximal_iff W P s]
  let Γ := W.inertiaSubgroup ℚ
  letI : Finite Γ := inferInstance
  letI : FaithfulSMul Γ W := by
    constructor
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    refine AlgEquiv.ext fun y => ?_
    rcases W.mem_or_inv_mem y with hy | hy
    · exact congrArg Subtype.val (hgh ⟨y, hy⟩)
    · have h1 : ((g : W.decompositionSubgroup ℚ) : K3 ≃ₐ[ℚ] K3) y⁻¹ =
          ((h : W.decompositionSubgroup ℚ) : K3 ≃ₐ[ℚ] K3) y⁻¹ :=
        congrArg Subtype.val (hgh ⟨y⁻¹, hy⟩)
      have h2 := congrArg (fun z : K3 => z⁻¹) h1
      simpa using h2
  have hdiv : Nat.card Γ ∣ 8 := by
    have h1 : Nat.card Γ ∣ Nat.card (W.decompositionSubgroup ℚ) :=
      Subgroup.card_subgroup_dvd_card Γ
    have h2 : Nat.card (W.decompositionSubgroup ℚ) ∣ Nat.card Gal(K3/ℚ) :=
      Subgroup.card_subgroup_dvd_card (W.decompositionSubgroup ℚ)
    have h := dvd_trans h1 h2
    have hcardGal : Nat.card Gal(K3/ℚ) = 8 := by
      calc
        Nat.card Gal(K3/ℚ) = Module.finrank ℚ K3 :=
          IsGalois.card_aut_eq_finrank ℚ K3
        _ = 8 := deningerQ8RootNumberNegOneTopField_finrank_over_rat
    rwa [hcardGal] at h
  have htwoUnit : IsUnit (⟨algebraMap ℤ K3 2, hAW 2⟩ : W) := by
    by_contra hnon
    exact htwo ((hcent 2).mp hnon)
  have htwoRes : ((2 : ℕ) : IsLocalRing.ResidueField W) ≠ 0 := by
    have hunit := htwoUnit.map (IsLocalRing.residue W)
    exact hunit.ne_zero
  have heightRes : ((8 : ℕ) : IsLocalRing.ResidueField W) ≠ 0 := by
    have heq : ((8 : ℕ) : IsLocalRing.ResidueField W) =
        ((2 : ℕ) : IsLocalRing.ResidueField W) ^ 3 := by norm_num
    rw [heq]
    exact pow_ne_zero 3 htwoRes
  have hcardRes : ((Nat.card Γ : ℕ) : IsLocalRing.ResidueField W) ≠ 0 := by
    intro hzero
    obtain ⟨c, hc⟩ := hdiv
    apply heightRes
    calc
      ((8 : ℕ) : IsLocalRing.ResidueField W) =
          ((Nat.card Γ * c : ℕ) : IsLocalRing.ResidueField W) := by rw [hc]
      _ = ((Nat.card Γ : ℕ) : IsLocalRing.ResidueField W) *
          ((c : ℕ) : IsLocalRing.ResidueField W) := by rw [Nat.cast_mul]
      _ = 0 := by rw [hzero, zero_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hcycΓ : IsCyclic Γ := by
    refine isCyclic_of_tame_of_natCard_ne_zero hπ hcardRes ?_
    intro g y
    exact ValuationInertia.smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y
  have hEq : P.inertia Gal(K3/ℚ) =
      Γ.map (W.decompositionSubgroup ℚ).subtype := by
    rw [← hcenterPrime]
    exact ValuationInertia.inertia_eq_map W hSW hact hW
  let e := Γ.equivMapOfInjective (W.decompositionSubgroup ℚ).subtype
    (Subgroup.subtype_injective _)
  have hcycMap : IsCyclic (Γ.map (W.decompositionSubgroup ℚ).subtype) := by
    letI : IsCyclic Γ := hcycΓ
    exact isCyclic_of_surjective e e.surjective
  rw [hEq]
  exact hcycMap

theorem deningerQ8_not_isCyclic : ¬ IsCyclic (QuaternionGroup 2) := by
  intro hcyc
  letI : IsCyclic (QuaternionGroup 2) := hcyc
  let a : QuaternionGroup 2 := QuaternionGroup.a (1 : ZMod 4)
  let x : QuaternionGroup 2 := QuaternionGroup.xa (0 : ZMod 4)
  have hcomm := IsCyclic.isMulCommutative.is_comm.comm a x
  dsimp [a, x] at hcomm
  injection hcomm with hz
  change ((-1 : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) at hz
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hz
  norm_num at hz

theorem q8Actual_odd_inertia_natCard_eq_four
    (p : ℤ) (hp : Prime p) (htwo : (2 : ℤ) ∉ Ideal.span {p})
    (x : 𝓞 K2) (hx : x ^ 2 = algebraMap ℤ (𝓞 K2) p)
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {p})) :
    Nat.card (P.inertia Gal(K3/ℚ)) = 4 := by
  let I := P.inertia Gal(K3/ℚ)
  have hcyc : IsCyclic I :=
    q8Actual_odd_inertia_isCyclic p hp htwo P hPover
  have hnot : ¬ I ≤ deningerQ8ActualCentralSubgroup :=
    q8Actual_odd_inertia_not_le_center p hp x hx P hPover
  have hcardGal : Nat.card Gal(K3/ℚ) = 8 := by
    calc
      Nat.card Gal(K3/ℚ) = Module.finrank ℚ K3 :=
        IsGalois.card_aut_eq_finrank ℚ K3
      _ = 8 := deningerQ8RootNumberNegOneTopField_finrank_over_rat
  have hdiv : Nat.card I ∣ 8 := by
    have h := Subgroup.card_subgroup_dvd_card I
    rwa [hcardGal] at h
  have hn1 : Nat.card I ≠ 1 := by
    intro hn
    apply hnot
    rw [(Subgroup.card_eq_one.mp hn)]
    exact bot_le
  have hn2 : Nat.card I ≠ 2 := by
    intro hn
    let e := deningerQ8RootNumberNegOne_galoisEquivQ8
    have hmapCard : Nat.card (I.map e.toMonoidHom) = 2 := by
      calc
        Nat.card (I.map e.toMonoidHom) = Nat.card I :=
          (Nat.card_congr
            (I.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
        _ = 2 := hn
    have hmap : I.map e.toMonoidHom = Subgroup.center (QuaternionGroup 2) :=
      deningerQ8_subgroup_eq_center_of_natCard_eq_two _ hmapCard
    have hIeq : I = deningerQ8ActualCentralSubgroup := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hmap, deningerQ8ActualCentralSubgroup_map_galoisEquivQ8]
    exact hnot (hIeq.le)
  have hn8 : Nat.card I ≠ 8 := by
    intro hn
    have htop : I = ⊤ :=
      Subgroup.eq_top_of_card_eq I (hn.trans hcardGal.symm)
    letI : IsCyclic I := hcyc
    have hsurj : Function.Surjective I.subtype := by
      intro g
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [htop]
      exact Subgroup.mem_top g
    have hcycGal : IsCyclic Gal(K3/ℚ) :=
      isCyclic_of_surjective I.subtype hsurj
    letI : IsCyclic Gal(K3/ℚ) := hcycGal
    have hcycQ8 : IsCyclic (QuaternionGroup 2) :=
      @isCyclic_of_surjective (QuaternionGroup 2) Gal(K3/ℚ) _ _ _ hcycGal _ _
        deningerQ8RootNumberNegOne_galoisEquivQ8.toMonoidHom
        deningerQ8RootNumberNegOne_galoisEquivQ8.surjective
    exact deningerQ8_not_isCyclic hcycQ8
  have hpos : 0 < Nat.card I := Nat.card_pos
  have hle : Nat.card I ≤ 8 := Nat.le_of_dvd (by norm_num) hdiv
  interval_cases hcard : Nat.card I
  all_goals simp_all

theorem q8Actual_five_inertia_natCard_eq_four
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    Nat.card (P.inertia Gal(K3/ℚ)) = 4 :=
  q8Actual_odd_inertia_natCard_eq_four 5 (by norm_num) (by
      intro h
      rcases Ideal.mem_span_singleton.mp h with ⟨c, hc⟩
      omega)
    q8BiquadFiveRoot q8BiquadFiveRoot_sq P hPover

theorem q8Actual_fortyOne_inertia_natCard_eq_four
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    Nat.card (P.inertia Gal(K3/ℚ)) = 4 :=
  q8Actual_odd_inertia_natCard_eq_four 41 (by norm_num) (by
      intro h
      rcases Ideal.mem_span_singleton.mp h with ⟨c, hc⟩
      omega)
    q8BiquadFortyOneRoot q8BiquadFortyOneRoot_sq P hPover

end

end RHTower
