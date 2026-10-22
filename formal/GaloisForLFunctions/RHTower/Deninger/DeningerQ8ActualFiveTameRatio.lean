import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualFiveInertiaCarrier
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8FroehlichLocalGaussianFactors
import GaloisForLFunctions.HTGeometry.DedekindResidueFieldAtPlace

/-!
# Actual Q8 tame ratio at 5

For every prime of the SST Q8 field above 5, localization supplies a discrete
valuation ring whose intrinsic tame inertia ratio is bijective onto residue
units. The residue field has five elements, so every quartic orientation has
the same normalized same-additive Gaussian phase, namely -1.

This removes an arbitrary identification of the actual inertia C4 with
(ZMod 5)ˣ from the p=5 local sign calculation.
-/

namespace RHTower

open scoped NumberField Pointwise
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ValuationInertia
noncomputable section

local instance q8FiveTameFactPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8FiveTameCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance q8FiveTameFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8FiveTameFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8FiveTameFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8FiveTameFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8FiveTameFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8FiveTameNumberFieldK3 : NumberField K3 := NumberField.mk
noncomputable local instance q8FiveTameIsGaloisRatK3 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
local instance q8FiveTameSpanFiveIsPrime : (Ideal.span {(5 : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime (by norm_num), Int.prime_iff_natAbs_prime]
  norm_num
local instance q8FiveTameSpanFiveIsMaximal : (Ideal.span {(5 : ℤ)}).IsMaximal :=
  Ideal.IsPrime.isMaximal (inferInstance : (Ideal.span {(5 : ℤ)}).IsPrime) (by
    intro h
    have : (5 : ℤ) = 0 := by
      rw [← Ideal.mem_bot, ← h]
      exact Ideal.mem_span_singleton_self 5
    norm_num at this)

/-- Precomposition by a multiplicative equivalence preserves the order of a character. -/
theorem orderOf_monoidHom_comp_mulEquiv_symm
    {G H K : Type*} [Group G] [CommGroup H] [Group K]
    (χ : G →* H) (e : G ≃* K) :
    orderOf (χ.comp e.symm.toMonoidHom) = orderOf χ := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro h
    apply MonoidHom.ext
    intro g
    have hg := congrArg (fun f : K →* H => f (e g)) h
    simpa [MonoidHom.comp_apply] using hg
  · intro h
    apply MonoidHom.ext
    intro k
    have hk := congrArg (fun f : G →* H => f (e.symm k)) h
    simpa [MonoidHom.comp_apply] using hk

/-- Passing between a multiplicative character and its unit-group homomorphism preserves order. -/
theorem orderOf_mulChar_ofUnitHom
    {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R']
    (f : Rˣ →* R'ˣ) :
    orderOf (MulChar.ofUnitHom f) = orderOf f := by
  calc
    orderOf (MulChar.ofUnitHom f) =
        orderOf (MulChar.mulEquivToUnitHom (MulChar.ofUnitHom f)) :=
      (MulChar.mulEquivToUnitHom.orderOf_eq _).symm
    _ = orderOf f := by simp

theorem q8OrderFourCharacter_orderOf : orderOf q8OrderFourCharacter = 4 := by
  change orderOf q8OrderFourCharacter = 2 ^ 2
  apply orderOf_eq_prime_pow
  · intro h
    have hg := congrArg
      (fun χ : Multiplicative (ZMod 4) →* ℂˣ =>
        χ (Multiplicative.ofAdd (1 : ZMod 4))) h
    exact q8OrderFourCharacter_generator_sq_ne_one (by
      simpa [MonoidHom.pow_apply] using hg)
  · apply MonoidHom.ext
    intro i
    let j : ZMod 4 := Multiplicative.toAdd i
    change ((q8OrderFourCharacter ^ 4) (Multiplicative.ofAdd j)) = 1
    apply Units.ext
    have hj : (q8OrderFourCharacter (Multiplicative.ofAdd j) : ℂ) ^ 4 = 1 := by
      rw [q8OrderFourCharacter_apply]
      calc
        (Complex.I ^ j.val) ^ 4 = (Complex.I ^ 4) ^ j.val := by
          rw [← pow_mul, mul_comm, pow_mul]
        _ = 1 := by norm_num [Complex.I_mul_I]
    simpa [MonoidHom.pow_apply] using hj

theorem q8CyclicSubgroupCharacter_orderOf :
    orderOf q8CyclicSubgroupCharacter = 4 := by
  rw [q8CyclicSubgroupCharacter]
  calc
    orderOf (q8OrderFourCharacter.comp q8CyclicSourceEquiv.symm.toMonoidHom) =
        orderOf q8OrderFourCharacter :=
      orderOf_monoidHom_comp_mulEquiv_symm q8OrderFourCharacter q8CyclicSourceEquiv
    _ = 4 := q8OrderFourCharacter_orderOf

theorem deningerQ8ActualCyclicSubgroupCharacter_orderOf :
    orderOf deningerQ8ActualCyclicSubgroupCharacter = 4 := by
  rw [deningerQ8ActualCyclicSubgroupCharacter]
  calc
    orderOf (q8CyclicSubgroupCharacter.comp
        deningerQ8ActualCyclicSubgroupEquiv.toMonoidHom) =
        orderOf q8CyclicSubgroupCharacter := by
      simpa using orderOf_monoidHom_comp_mulEquiv_symm
        q8CyclicSubgroupCharacter deningerQ8ActualCyclicSubgroupEquiv.symm
    _ = 4 := q8CyclicSubgroupCharacter_orderOf

/-- Actual quartic source character restricted along the literal equality `I₅ = C₄`. -/
def q8ActualFiveInertiaSourceCharacter
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    LinearCharacter (P.inertia Gal(K3/ℚ)) :=
  deningerQ8ActualCyclicSubgroupCharacter.comp
    (MulEquiv.subgroupCongr
      (q8Actual_five_inertia_eq_cyclicSource P hPover)).toMonoidHom

theorem q8ActualFiveInertiaSourceCharacter_orderOf
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    orderOf (q8ActualFiveInertiaSourceCharacter P hPover) = 4 := by
  unfold q8ActualFiveInertiaSourceCharacter
  let e : P.inertia Gal(K3/ℚ) ≃* deningerQ8ActualCyclicSubgroup :=
    MulEquiv.subgroupCongr (q8Actual_five_inertia_eq_cyclicSource P hPover)
  calc
    orderOf (deningerQ8ActualCyclicSubgroupCharacter.comp e.toMonoidHom) =
        orderOf deningerQ8ActualCyclicSubgroupCharacter := by
      simpa [e] using orderOf_monoidHom_comp_mulEquiv_symm
        deningerQ8ActualCyclicSubgroupCharacter e.symm
    _ = 4 := deningerQ8ActualCyclicSubgroupCharacter_orderOf




theorem q8Actual_five_inertiaDeg_eq_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    P.inertiaDeg ℤ = 1 := by
  letI : P.LiesOver (Ideal.span {(5 : ℤ)}) := hPover
  have hcard := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (Ideal.span {(5 : ℤ)}) P (G := Gal(K3/ℚ))
  rw [q8Actual_five_decomposition_eq_inertia P hPover,
    q8Actual_five_inertia_natCard_eq_four P hPover] at hcard
  omega

theorem q8Actual_five_residue_natCard_eq_five
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    Nat.card ((𝓞 K3) ⧸ P) = 5 := by
  letI : P.LiesOver (Ideal.span {(5 : ℤ)}) := hPover
  calc
    Nat.card ((𝓞 K3) ⧸ P) = Submodule.cardQuot P := by
      rw [Submodule.cardQuot_apply]
    _ = Ideal.absNorm P := (Ideal.absNorm_apply P).symm
    _ = 5 ^ (Ideal.span {(5 : ℤ)}).inertiaDeg' P :=
      Ideal.absNorm_eq_pow_inertiaDeg' P Nat.prime_five
    _ = 5 ^ P.inertiaDeg ℤ := by
      rw [Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(5 : ℤ)}) P]
    _ = 5 := by rw [q8Actual_five_inertiaDeg_eq_one P hPover]; norm_num

theorem zmodFive_quarticChar_neg_one_eq_neg_one
    (χ : MulChar (ZMod 5) ℂ) (horder : orderOf χ = 4) :
    χ (-1) = -1 := by
  have hsqne : χ ^ 2 ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · norm_num
    · rw [horder]
      norm_num
  have hvalueSq : χ (-1) ^ 2 = 1 := by
    rw [← map_pow]
    norm_num
  rcases sq_eq_one_iff.mp hvalueSq with hpos | hneg
  · exfalso
    apply hsqne
    apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have hu4 : ((u : ZMod 5) ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      norm_num
      exact congrArg Units.val (ZMod.units_pow_card_sub_one_eq_one 5 u)
    rcases sq_eq_one_iff.mp hu4 with hu | hu
    · rw [← map_pow, hu, map_one]
    · rw [← map_pow, hu, hpos]
  · exact hneg

theorem zmodFive_quarticSameAdditiveGaussProduct_eq_neg_five
    (χ : MulChar (ZMod 5) ℂ) (horder : orderOf χ = 4) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = -5 := by
  have hne : χ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    norm_num at horder
  have h := gaussSum_mul_gaussSum_pow_orderOf_sub_one
    (χ := χ) (ψ := ZMod.stdAddChar) hne (ZMod.isPrimitive_stdAddChar 5)
  rw [horder] at h
  norm_num [zmodFive_quarticChar_neg_one_eq_neg_one χ horder] at h ⊢
  have hfour : χ ^ 4 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one χ
  have hthree : χ ^ 3 = χ⁻¹ := by
    calc
      χ ^ 3 = χ ^ 3 * 1 := (mul_one _).symm
      _ = χ ^ 3 * (χ * χ⁻¹) := by simp
      _ = χ ^ 4 * χ⁻¹ := by rw [← mul_assoc, ← pow_succ]
      _ = χ⁻¹ := by rw [hfour, one_mul]
  simpa [hthree] using h

theorem zmodFive_quarticSameAdditiveGaussianPhase_eq_neg_one
    (χ : MulChar (ZMod 5) ℂ) (horder : orderOf χ = 4) :
    (5 : ℂ)⁻¹ *
      (gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar) = -1 := by
  rw [zmodFive_quarticSameAdditiveGaussProduct_eq_neg_five χ horder]
  norm_num

/-- Intrinsic passage from actual five-adic inertia to units of the prime residue field. -/
noncomputable def q8ActualFiveSourceToZModUnitsEquiv
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (_hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    P.inertia Gal(K3/ℚ) ≃* (ZMod 5)ˣ := by
  letI : IsDiscreteValuationRing W := dvr
  letI : Finite (IsLocalRing.ResidueField W) := finiteRes
  let ratio := residueRatioHom hπ
    (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
      smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)
  let eRatio : W.inertiaSubgroup ℚ ≃* (IsLocalRing.ResidueField W)ˣ :=
    MulEquiv.ofBijective ratio.toHomUnits hRatioBij
  letI : Fintype (IsLocalRing.ResidueField W) := Fintype.ofFinite _
  let eRes : ZMod 5 ≃+* IsLocalRing.ResidueField W :=
    ZMod.ringEquivOfPrime _ Nat.prime_five (by
      simpa [Nat.card_eq_fintype_card] using hResidueCard)
  exact (eI.trans eRatio).trans (Units.mapEquiv eRes.toMulEquiv).symm

/-- Actual quartic source character transported to the canonical five-element residue model. -/
noncomputable def q8ActualFiveZModSourceCharacter
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    MulChar (ZMod 5) ℂ :=
  MulChar.ofUnitHom ((q8ActualFiveInertiaSourceCharacter P hPover).comp
    (q8ActualFiveSourceToZModUnitsEquiv P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij).symm.toMonoidHom)

/-- Pullback through the intrinsic tame equivalence recovers the literal inertia source. -/
theorem q8ActualFiveZModSourceCharacter_pullback
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij).toUnitHom.comp
        (q8ActualFiveSourceToZModUnitsEquiv P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij).toMonoidHom =
      q8ActualFiveInertiaSourceCharacter P hPover := by
  apply MonoidHom.ext
  intro g
  simp [q8ActualFiveZModSourceCharacter, MulChar.toUnitHom_eq]

/-- Tame and residue transport preserves the source character's exact order four. -/
theorem q8ActualFiveZModSourceCharacter_orderOf
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    orderOf (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij) = 4 := by
  unfold q8ActualFiveZModSourceCharacter
  rw [orderOf_mulChar_ofUnitHom]
  calc
    orderOf ((q8ActualFiveInertiaSourceCharacter P hPover).comp
        (q8ActualFiveSourceToZModUnitsEquiv P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij).symm.toMonoidHom) =
        orderOf (q8ActualFiveInertiaSourceCharacter P hPover) :=
      orderOf_monoidHom_comp_mulEquiv_symm _ _
    _ = 4 := q8ActualFiveInertiaSourceCharacter_orderOf P hPover

/-- The actual source-selected five-adic character has normalized local phase `-1`. -/
theorem q8ActualFiveZModSourceCharacter_phase
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    (5 : ℂ)⁻¹ *
      (gaussSum (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij) ZMod.stdAddChar *
        gaussSum (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij)⁻¹ ZMod.stdAddChar) = -1 :=
  zmodFive_quarticSameAdditiveGaussianPhase_eq_neg_one _
    (q8ActualFiveZModSourceCharacter_orderOf P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij)

def Q8ActualFiveTameRatioRealization
    (P : Ideal (𝓞 K3))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W) : Prop := by
  letI : IsDiscreteValuationRing W := dvr
  exact ∃ (π : W) (hπ : Irreducible π),
    Nat.card (IsLocalRing.ResidueField W) = 5 ∧
    Finite (IsLocalRing.ResidueField W) ∧
    Nonempty (P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ) ∧
    Function.Bijective
      (GaloisForLFunctions.HTGeometry.residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits

theorem q8Actual_five_tameRatioRealization_exists
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    ∃ (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W),
      Q8ActualFiveTameRatioRealization P W dvr := by
  letI : P.LiesOver (Ideal.span {(5 : ℤ)}) := hPover
  have hPfive : algebraMap ℤ (𝓞 K3) 5 ∈ P :=
    (Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance)
      (by norm_num : Prime (5 : ℤ))).mp hPover
  have hPne : P ≠ ⊥ := by
    intro hP
    rw [hP, Ideal.mem_bot] at hPfive
    have hcast : (5 : 𝓞 K3) = ((0 : ℤ) : 𝓞 K3) := by simpa using hPfive
    norm_num at hcast
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K3) :=
    ⟨P, (inferInstance : P.IsPrime), hPne⟩
  let W : ValuationSubring K3 :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K3 v
  letI : IsLocalization P.primeCompl W :=
    IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime v
  letI dvr : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) hPne W
  have hW : W ≠ ⊤ := ValuationSubring.ne_top_of_isDiscreteValuationRing W
  have hSW : ∀ s : 𝓞 K3, algebraMap (𝓞 K3) K3 s ∈ W := by
    intro s
    exact (algebraMap (𝓞 K3) W s).property
  have hact : ∀ (g : Gal(K3/ℚ)) (s : 𝓞 K3),
      algebraMap (𝓞 K3) K3 (g • s) = g • algebraMap (𝓞 K3) K3 s := by
    intro g s
    rfl
  have hcenterPrime : centerPrime W hSW = P := by
    apply Ideal.ext
    intro s
    change toValuationSubring W hSW s ∈
        IsLocalRing.maximalIdeal W ↔ s ∈ P
    have heq : toValuationSubring W hSW s = algebraMap (𝓞 K3) W s := Subtype.ext rfl
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
  have hEq : P.inertia Gal(K3/ℚ) =
      Γ.map (W.decompositionSubgroup ℚ).subtype := by
    rw [← hcenterPrime]
    exact inertia_eq_map W hSW hact hW
  let eI : P.inertia Gal(K3/ℚ) ≃* Γ :=
    (MulEquiv.subgroupCongr hEq).trans
      (Γ.equivMapOfInjective (W.decompositionSubgroup ℚ).subtype
        (Subgroup.subtype_injective _)).symm
  let eRes : ((𝓞 K3) ⧸ P) ≃+* IsLocalRing.ResidueField W :=
    (quotientEquivIdealResidueField P).trans
      (IsLocalRing.ResidueField.mapEquiv
        (placeLocalizationAlgEquiv K3 v).toRingEquiv)
  letI : Finite (IsLocalRing.ResidueField W) :=
    Finite.of_injective eRes.symm eRes.symm.injective
  have hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5 := by
    calc
      Nat.card (IsLocalRing.ResidueField W) = Nat.card ((𝓞 K3) ⧸ P) :=
        Nat.card_congr eRes.toEquiv.symm
      _ = 5 := q8Actual_five_residue_natCard_eq_five P hPover
  have hΓcard : Nat.card Γ = 4 := by
    calc
      Nat.card Γ = Nat.card (P.inertia Gal(K3/ℚ)) :=
        Nat.card_congr eI.toEquiv.symm
      _ = 4 := q8Actual_five_inertia_natCard_eq_four P hPover
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  let hres : ∀ (g : Γ) (y : W),
      g • y - y ∈ IsLocalRing.maximalIdeal W :=
    fun g y => smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y
  let ratio := GaloisForLFunctions.HTGeometry.residueRatioHom hπ hres
  have hfourRes : ((4 : ℕ) : IsLocalRing.ResidueField W) ≠ 0 := by
    haveI : Fintype (IsLocalRing.ResidueField W) := Fintype.ofFinite _
    let eRes : ZMod 5 ≃+* IsLocalRing.ResidueField W :=
      ZMod.ringEquivOfPrime _ Nat.prime_five (by
        simpa [Nat.card_eq_fintype_card] using hResidueCard)
    intro h
    have h' : eRes (4 : ZMod 5) = eRes 0 := by
      calc
        eRes (4 : ZMod 5) = (4 : IsLocalRing.ResidueField W) := map_natCast eRes 4
        _ = 0 := h
        _ = eRes 0 := (map_zero eRes).symm
    have hz : (4 : ZMod 5) ≠ 0 := by
      intro hz
      change ((4 : ℤ) : ZMod 5) = ((0 : ℤ) : ZMod 5) at hz
      rw [ZMod.intCast_eq_intCast_iff'] at hz
      norm_num at hz
    exact hz (eRes.injective h')
  have hratioInj : Function.Injective ratio :=
    GaloisForLFunctions.HTGeometry.residueRatioHom_injective_of_natCard_ne_zero
      hπ (by simpa [hΓcard] using hfourRes) hres
  have hratioUnitsInj : Function.Injective ratio.toHomUnits := by
    intro x y hxy
    apply hratioInj
    exact congrArg Units.val hxy
  have hratioUnitsBij : Function.Bijective ratio.toHomUnits := by
    apply (Nat.bijective_iff_injective_and_card ratio.toHomUnits).2
    refine ⟨hratioUnitsInj, ?_⟩
    rw [hΓcard, Nat.card_units, hResidueCard]
  exact ⟨W, dvr, π, hπ, hResidueCard, inferInstance, ⟨eI⟩, hratioUnitsBij⟩

/-- A five-adic tame model carries the literal SST source character to `ZMod 5`,
recovers it on pullback, preserves exact order four, and has phase `-1`. -/
def Q8ActualFiveSourceCharacterRealization
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W) : Prop := by
  letI : IsDiscreteValuationRing W := dvr
  exact ∃ (finiteRes : Finite (IsLocalRing.ResidueField W))
      (π : W) (hπ : Irreducible π)
      (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
      (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
      (hRatioBij : Function.Bijective
        (residueRatioHom hπ
          (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
            smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits),
    (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
        hResidueCard hRatioBij).toUnitHom.comp
          (q8ActualFiveSourceToZModUnitsEquiv P hPover W dvr finiteRes π hπ eI
            hResidueCard hRatioBij).toMonoidHom =
        q8ActualFiveInertiaSourceCharacter P hPover ∧
    orderOf (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij) = 4 ∧
    (5 : ℂ)⁻¹ *
      (gaussSum (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij) ZMod.stdAddChar *
        gaussSum (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij)⁻¹ ZMod.stdAddChar) = -1

theorem q8Actual_five_sourceCharacterRealization_of_tameRatioRealization
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (hTame : Q8ActualFiveTameRatioRealization P W dvr) :
    Q8ActualFiveSourceCharacterRealization P hPover W dvr := by
  letI : IsDiscreteValuationRing W := dvr
  simp only [Q8ActualFiveTameRatioRealization] at hTame
  rcases hTame with ⟨π, hπ, hResidueCard, finiteRes, ⟨eI⟩, hRatioBij⟩
  unfold Q8ActualFiveSourceCharacterRealization
  exact ⟨finiteRes, π, hπ, eI, hResidueCard, hRatioBij,
    q8ActualFiveZModSourceCharacter_pullback P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij,
    q8ActualFiveZModSourceCharacter_orderOf P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij,
    q8ActualFiveZModSourceCharacter_phase P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij⟩

/-- Every actual prime over `5` realizes the source-selected quartic character with phase `-1`. -/
theorem q8Actual_five_sourceCharacterRealization_exists
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    ∃ (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W),
      Q8ActualFiveSourceCharacterRealization P hPover W dvr := by
  rcases q8Actual_five_tameRatioRealization_exists P hPover with ⟨W, dvr, hTame⟩
  exact ⟨W, dvr,
    q8Actual_five_sourceCharacterRealization_of_tameRatioRealization
      P hPover W dvr hTame⟩

end
end RHTower
