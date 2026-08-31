import GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicDecomposition
import GaloisForLFunctions.HTGeometry.DVRFiniteSpan

/-!
# Literal wild two-adic break of the SST quaternion field

The exact ramification index at two is converted into a normalized local
valuation identity by identifying principal-ideal colength with DVR order.
For the literal top radical `z`, its defining equation has the form

`z² = 2 b`,

where an explicit Bezout computation proves that `b` is a unit at every prime
above two.  Hence `z` is a uniformizer.  The source-selected central inertia
involution sends `z` to `-z`, so its displacement is `-2z` and has exact order
three.  This supplies a coefficient-faithful wild-break datum on the same
local decomposition carrier as the primitive quartic source character.
-/

namespace RHTower

open scoped NumberField Pointwise
open IsDiscreteValuationRing
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8WildCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

noncomputable local instance q8WildFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8WildFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8WildFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8WildFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8WildFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8WildNumberFieldK3 : NumberField K3 := NumberField.mk

/-- In a DVR, colength of a nonzero principal ideal is its additive valuation. -/
theorem dvr_length_quotient_span_eq_addVal
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {x : B} (hx : x ≠ 0) :
    Module.length B (B ⧸ Ideal.span {x}) = addVal B x := by
  obtain ⟨pi, hpi⟩ := exists_irreducible B
  obtain ⟨n, hval, hspan⟩ :=
    GaloisForLFunctions.HTGeometry.exists_span_singleton_eq_span_pow hpi hx
  rw [hspan, ← Ideal.span_singleton_pow, ← hpi.maximalIdeal_eq,
    length_quotient_pow_maximalIdeal, hval]

/-- Exact valuation of two in every localization at a prime above two. -/
theorem q8Literal_two_local_addVal_two_eq_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let B := Localization.AtPrime P
    letI : IsDiscreteValuationRing B :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (𝓞 K3) (show P ≠ ⊥ from by
          intro hP
          rw [hP, Ideal.mem_bot] at hPtwo
          norm_num at hPtwo) B
    addVal B (2 : B) = 2 := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hPover : P.LiesOver p := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) Int.prime_two]
    simpa [p] using hPtwo
  letI : P.LiesOver p := hPover
  let B := Localization.AtPrime P
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) B
  letI : CharZero B := charZero_of_injective_algebraMap
    (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)
  have hram : P.ramificationIdx ℤ = 2 :=
    q8Literal_two_ramificationIdx_eq_two P hPtwo
  have hlen :
      (Module.length B (B ⧸ p.map (algebraMap ℤ B))).toNat = 2 := by
    rw [← Ideal.ramificationIdx_eq p P]
    exact hram
  have hmap : p.map (algebraMap ℤ B) = Ideal.span {(2 : B)} := by
    simp [p, Ideal.map_span]
  rw [hmap, dvr_length_quotient_span_eq_addVal (by norm_num : (2 : B) ≠ 0)] at hlen
  have hfinite : addVal B (2 : B) ≠ ⊤ := by
    rw [Ne, addVal_eq_top_iff]
    norm_num
  calc
    addVal B (2 : B) = ((addVal B (2 : B)).toNat : ℕ∞) :=
      (ENat.coe_toNat hfinite).symm
    _ = 2 := by rw [hlen]; norm_num

/-- Unit coefficient multiplying two in the literal top radical relation. -/
noncomputable def q8LiteralTwoAdicUnitCoefficient : 𝓞 K3 :=
  (q8LiteralTwoAdicU + 2) * (35 + 12 * q8LiteralTwoAdicV)

/-- The coefficient in `z² = 2b` remains a unit at every prime over two. -/
theorem q8Literal_two_local_unitCoefficient_isUnit
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    IsUnit (algebraMap (𝓞 K3) (Localization.AtPrime P)
      q8LiteralTwoAdicUnitCoefficient) := by
  let B := Localization.AtPrime P
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) B
  letI : CharZero B := charZero_of_injective_algebraMap
    (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)
  let f : 𝓞 K3 →+* B := algebraMap (𝓞 K3) B
  let u : B := f q8LiteralTwoAdicU
  let v : B := f q8LiteralTwoAdicV
  have hu : u ^ 2 = u + 1 := by
    dsimp [u]
    rw [← map_one f]
    simpa only [map_pow, map_add] using congrArg f q8LiteralTwoAdicU_sq
  have hv : v ^ 2 = v + 10 := by
    dsimp [v]
    rw [← map_ofNat f 10]
    simpa only [map_pow, map_add] using congrArg f q8LiteralTwoAdicV_sq
  have htwoVal : addVal B (2 : B) = 2 :=
    q8Literal_two_local_addVal_two_eq_two P hPtwo
  have htwoNonunit : ¬ IsUnit (2 : B) := by
    intro hunit
    have hzero := GaloisForLFunctions.HTGeometry.addVal_of_isUnit_target hunit
    rw [htwoVal] at hzero
    norm_num at hzero
  have hotherNonunit : ¬ IsUnit ((-512 : B) * 2) := by
    intro hunit
    exact htwoNonunit (IsUnit.mul_iff.mp hunit).2
  have hoddUnit : IsUnit (1025 : B) := by
    have hsum : (1025 : B) + (-512 : B) * 2 = 1 := by norm_num
    exact (IsLocalRing.isUnit_or_isUnit_of_add_one hsum).resolve_right hotherNonunit
  let b : B := (u + 2) * (35 + 12 * v)
  let c : B := (3 - u) * (47 - 12 * v)
  have hbc : b * c = 1025 := by
    dsimp [b, c]
    calc
      (u + 2) * (35 + 12 * v) * ((3 - u) * (47 - 12 * v)) =
          ((u + 2) * (3 - u)) * ((35 + 12 * v) * (47 - 12 * v)) := by ring
      _ = 5 * 205 := by
        rw [show (u + 2) * (3 - u) = 5 by
          calc
            (u + 2) * (3 - u) = 6 + u - u ^ 2 := by ring
            _ = 5 := by rw [hu]; ring]
        rw [show (35 + 12 * v) * (47 - 12 * v) = 205 by
          calc
            (35 + 12 * v) * (47 - 12 * v) = 1645 + 144 * v - 144 * v ^ 2 := by ring
            _ = 205 := by rw [hv]; ring]
      _ = 1025 := by norm_num
  have hbUnit : IsUnit b := by
    exact (IsUnit.mul_iff.mp (hbc ▸ hoddUnit)).1
  simpa only [q8LiteralTwoAdicUnitCoefficient, map_mul, map_add, map_ofNat,
    b, u, v, f] using hbUnit

/-- The top radical is a uniformizer at every prime above two. -/
theorem q8Literal_two_local_addVal_topRadical_eq_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let B := Localization.AtPrime P
    letI : IsDiscreteValuationRing B :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (𝓞 K3) (show P ≠ ⊥ from by
          intro hP
          rw [hP, Ideal.mem_bot] at hPtwo
          norm_num at hPtwo) B
    addVal B (algebraMap (𝓞 K3) B q8LiteralTwoAdicZ) = 1 := by
  let B := Localization.AtPrime P
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) B
  letI : CharZero B := charZero_of_injective_algebraMap
    (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)
  let f : 𝓞 K3 →+* B := algebraMap (𝓞 K3) B
  let z : B := f q8LiteralTwoAdicZ
  let b : B := f q8LiteralTwoAdicUnitCoefficient
  change addVal B z = 1
  have hbUnit : IsUnit b := q8Literal_two_local_unitCoefficient_isUnit P hPtwo
  have hbVal : addVal B b = 0 :=
    GaloisForLFunctions.HTGeometry.addVal_of_isUnit_target hbUnit
  have htwoVal : addVal B (2 : B) = 2 :=
    q8Literal_two_local_addVal_two_eq_two P hPtwo
  have hz : z ^ 2 = 2 * b := by
    dsimp [z, b, q8LiteralTwoAdicUnitCoefficient]
    rw [← map_ofNat f 2]
    simpa only [map_pow, map_mul, map_add, map_ofNat, mul_assoc] using
      congrArg f q8LiteralTwoAdicZ_sq
  have hz0 : z ≠ 0 := by
    intro hzzero
    rw [hzzero, zero_pow (by norm_num : 2 ≠ 0)] at hz
    have h2b : (2 : B) * b ≠ 0 := mul_ne_zero (by norm_num) hbUnit.ne_zero
    exact h2b hz.symm
  have hvaleq : 2 • addVal B z = 2 := by
    calc
      2 • addVal B z = addVal B (z ^ 2) := (addVal_pow z 2).symm
      _ = addVal B (2 * b) := congrArg (addVal B) hz
      _ = 2 := by rw [addVal_mul, htwoVal, hbVal]; norm_num
  have hfinite : addVal B z ≠ ⊤ := by
    rw [Ne, addVal_eq_top_iff]
    exact hz0
  have hspec : addVal B z = ((addVal B z).toNat : ℕ∞) :=
    (ENat.coe_toNat hfinite).symm
  have hnat : 2 * (addVal B z).toNat = 2 := by
    rw [hspec] at hvaleq
    change ((2 * (addVal B z).toNat : ℕ) : ℕ∞) = (2 : ℕ∞) at hvaleq
    exact ENat.coe_inj.mp hvaleq
  have : (addVal B z).toNat = 1 := by omega
  rw [hspec, this]
  norm_num

/-- The literal central inertia involution moves the top radical by `-2z`. -/
theorem q8Literal_centralInvolution_sub_topRadical :
    q8CAlgEquiv • q8LiteralTwoAdicZ - q8LiteralTwoAdicZ =
      -2 * q8LiteralTwoAdicZ := by
  apply Subtype.ext
  change q8CAlgEquiv deningerQ8RootNumberNegOneTopRoot -
      deningerQ8RootNumberNegOneTopRoot = -2 * deningerQ8RootNumberNegOneTopRoot
  rw [q8CAlgEquiv_apply, q8C_root]
  ring

/-- Exact lower-break datum: central inertia displacement has order three. -/
theorem q8Literal_two_local_addVal_centralDisplacement_eq_three
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let B := Localization.AtPrime P
    letI : IsDiscreteValuationRing B :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (𝓞 K3) (show P ≠ ⊥ from by
          intro hP
          rw [hP, Ideal.mem_bot] at hPtwo
          norm_num at hPtwo) B
    addVal B (algebraMap (𝓞 K3) B
      (q8CAlgEquiv • q8LiteralTwoAdicZ - q8LiteralTwoAdicZ)) = 3 := by
  let B := Localization.AtPrime P
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) B
  letI : CharZero B := charZero_of_injective_algebraMap
    (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)
  let f : 𝓞 K3 →+* B := algebraMap (𝓞 K3) B
  change addVal B (f
    (q8CAlgEquiv • q8LiteralTwoAdicZ - q8LiteralTwoAdicZ)) = 3
  have htwoVal : addVal B (2 : B) = 2 :=
    q8Literal_two_local_addVal_two_eq_two P hPtwo
  have hzVal : addVal B (f q8LiteralTwoAdicZ) = 1 :=
    q8Literal_two_local_addVal_topRadical_eq_one P hPtwo
  have hnegTwoVal : addVal B (-2 : B) = 2 := by
    rw [show (-2 : B) = (-1) * 2 by ring, addVal_mul,
      GaloisForLFunctions.HTGeometry.addVal_of_isUnit_target isUnit_one.neg,
      htwoVal]
    norm_num
  rw [q8Literal_centralInvolution_sub_topRadical, map_mul, map_neg, map_ofNat,
    addVal_mul, hnegTwoVal, hzVal]
  norm_num

end
end RHTower
