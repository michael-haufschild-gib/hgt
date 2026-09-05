import GaloisForLFunctions.RHTower.DeningerQ8ActualBiquadraticDiscriminant
import GaloisForLFunctions.HTGeometry.UnramifiedRadicalCriterion
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Odd ramification of the actual Q8 maximal abelian field

The existing discriminant calculation proved only that every prime divisor of
`disc(ℚ(√5,√41))` is `5` or `41`. This file proves the missing converse from the literal
integral square roots: an unramified prime has valuation one, whereas a square has even valuation.
Thus both `5` and `41` ramify, and the discriminant has exact prime support `{5,41}`.
-/

open IsDiscreteValuationRing

namespace RHTower

open scoped NumberField

noncomputable section

/-- An integral square root of a rational prime forces every prime above it to ramify.  Locally,
an unramified rational prime is a uniformizer, but a square has even additive valuation. -/
theorem prime_not_isUnramifiedAt_of_integral_square
    {K : Type*} [Field K] [NumberField K]
    (p : ℤ) (hp : Prime p) (z : 𝓞 K)
    (hz : z ^ 2 = algebraMap ℤ (𝓞 K) p)
    (P : Ideal (𝓞 K)) [P.IsPrime]
    (hPover : P.LiesOver (Ideal.span {p})) :
    ¬ Algebra.IsUnramifiedAt ℤ P := by
  intro hunramified
  letI : (Ideal.span {p}).IsMaximal := hp.isMaximal_span_singleton
  have hPp : algebraMap ℤ (𝓞 K) p ∈ P := by
    exact (Ideal.liesOver_span_iff (inferInstance : P.IsPrime).ne_top hp).mp hPover
  have hPne : P ≠ ⊥ := by
    intro hP
    rw [hP, Ideal.mem_bot] at hPp
    have hcast : (p : 𝓞 K) = ((0 : ℤ) : 𝓞 K) := by simpa using hPp
    exact hp.ne_zero (Int.cast_injective hcast)
  let B := Localization.AtPrime P
  letI : Algebra (Localization.AtPrime (Ideal.span {p})) B :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.span {p}) P
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hPne B
  letI : CharZero B := charZero_of_injective_algebraMap
    (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)
  have hmap :
      (Ideal.span {p}).map (algebraMap ℤ B) = IsLocalRing.maximalIdeal B :=
    ((Algebra.isUnramifiedAt_iff_map_eq ℤ (Ideal.span {p}) P).mp
      hunramified).2
  have hspan :
      Ideal.span {(algebraMap ℤ B p)} = IsLocalRing.maximalIdeal B := by
    simpa [Ideal.map_span] using hmap
  have hpBne : algebraMap ℤ B p ≠ 0 := by
    intro h
    have hcast : (p : B) = ((0 : ℤ) : B) := by simpa using h
    exact hp.ne_zero (Int.cast_injective hcast)
  have hpIrreducible : Irreducible (algebraMap ℤ B p) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
      (algebraMap ℤ B p) hpBne hspan.symm
  have hpVal : addVal B (algebraMap ℤ B p) = 1 := by
    simpa using GaloisForLFunctions.HTGeometry.addVal_pow_uniformizer hpIrreducible 1
  let f : 𝓞 K →+* B := algebraMap (𝓞 K) B
  have hzB : (f z) ^ 2 = algebraMap ℤ B p := by
    change (algebraMap (𝓞 K) B z) ^ 2 = algebraMap ℤ B p
    calc
      (algebraMap (𝓞 K) B z) ^ 2 =
          algebraMap (𝓞 K) B (algebraMap ℤ (𝓞 K) p) := by
        simpa only [map_pow] using congrArg (algebraMap (𝓞 K) B) hz
      _ = algebraMap ℤ B p :=
        (IsScalarTower.algebraMap_apply ℤ (𝓞 K) B p).symm
  have hdvd : 2 ∣ 1 :=
    GaloisForLFunctions.HTGeometry.dvd_of_addVal_pow_mul_unit
      (B := B) (p := algebraMap ℤ B p) (b := 1) (z := f z)
      (k := 1) (r := 2) hpVal
      (GaloisForLFunctions.HTGeometry.addVal_of_isUnit_target isUnit_one)
      (by simpa using hzB)
  norm_num at hdvd

/-- An integral square root of a rational prime forces that prime to divide the number-field
discriminant. This is the global corollary of the every-local-prime obstruction. -/
theorem prime_dvd_numberField_discr_of_integral_square
    {K : Type*} [Field K] [NumberField K]
    (p : ℤ) (hp : Prime p) (z : 𝓞 K)
    (hz : z ^ 2 = algebraMap ℤ (𝓞 K) p) :
    p ∣ NumberField.discr K := by
  by_contra hpd
  have hunramified :
      Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {p}) :=
    (NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) hp).mp hpd
  letI : (Ideal.span {p}).IsMaximal := hp.isMaximal_span_singleton
  obtain ⟨P, hPMax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 K) (Ideal.span {p})
  letI : P.IsPrime := hPMax.isPrime
  exact prime_not_isUnramifiedAt_of_integral_square p hp z hz P hPover
    (hunramified P inferInstance hPover)

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

local instance deningerQ8ActualBiquadraticOddRamificationLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective

noncomputable local instance deningerQ8ActualBiquadraticOddRamificationLocalInst2 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis

noncomputable local instance deningerQ8ActualBiquadraticOddRamificationLocalInst3 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis

noncomputable local instance deningerQ8ActualBiquadraticOddRamificationLocalInst4 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis

noncomputable local instance deningerQ8ActualBiquadraticOddRamificationLocalInst5 : NumberField K2 := NumberField.mk

/-- Literal integral `√5` in the actual maximal abelian subfield. -/
noncomputable def q8BiquadFiveRoot : 𝓞 K2 :=
  ⟨2 * (algebraMap K1 K2) q8BiquadU - 1,
    (isIntegral_natCast 2).mul
      (q8BiquadU_isIntegral.map (IsScalarTower.toAlgHom ℤ K1 K2)) |>.sub
        (isIntegral_natCast 1)⟩

theorem q8BiquadFiveRoot_sq :
    q8BiquadFiveRoot ^ 2 = algebraMap ℤ (𝓞 K2) 5 := by
  apply Subtype.ext
  change (2 * (algebraMap K1 K2) q8BiquadU - 1) ^ 2 = (5 : K2)
  have hu : ((algebraMap K1 K2) q8BiquadU) ^ 2 =
      (algebraMap K1 K2) q8BiquadU + 1 := by
    simpa only [map_pow, map_add, map_one] using
      congrArg (algebraMap K1 K2) q8BiquadU_sq
  calc
    (2 * (algebraMap K1 K2) q8BiquadU - 1) ^ 2 =
        4 * ((algebraMap K1 K2) q8BiquadU) ^ 2 -
          4 * (algebraMap K1 K2) q8BiquadU + 1 := by ring
    _ = 5 := by rw [hu]; ring

/-- Literal integral `√41` in the actual maximal abelian subfield. -/
noncomputable def q8BiquadFortyOneRoot : 𝓞 K2 :=
  ⟨2 * q8BiquadV - 1,
    (isIntegral_natCast 2).mul q8BiquadV_isIntegral |>.sub (isIntegral_natCast 1)⟩

theorem q8BiquadFortyOneRoot_sq :
    q8BiquadFortyOneRoot ^ 2 = algebraMap ℤ (𝓞 K2) 41 := by
  apply Subtype.ext
  change (2 * q8BiquadV - 1) ^ 2 = (41 : K2)
  calc
    (2 * q8BiquadV - 1) ^ 2 =
        4 * q8BiquadV ^ 2 - 4 * q8BiquadV + 1 := by ring
    _ = 41 := by rw [q8BiquadV_sq]; ring

/-- Every prime of the actual maximal abelian subfield above `5` is ramified. -/
theorem q8Biquad_five_not_isUnramifiedAt
    (P : Ideal (𝓞 K2)) [P.IsPrime]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    ¬ Algebra.IsUnramifiedAt ℤ P :=
  prime_not_isUnramifiedAt_of_integral_square 5 (by norm_num)
    q8BiquadFiveRoot q8BiquadFiveRoot_sq P hPover

/-- Every prime of the actual maximal abelian subfield above `41` is ramified. -/
theorem q8Biquad_fortyOne_not_isUnramifiedAt
    (P : Ideal (𝓞 K2)) [P.IsPrime]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    ¬ Algebra.IsUnramifiedAt ℤ P :=
  prime_not_isUnramifiedAt_of_integral_square 41 (by norm_num)
    q8BiquadFortyOneRoot q8BiquadFortyOneRoot_sq P hPover

theorem q8Biquad_five_dvd_discr :
    (5 : ℤ) ∣ NumberField.discr K2 :=
  prime_dvd_numberField_discr_of_integral_square 5 (by norm_num)
    q8BiquadFiveRoot q8BiquadFiveRoot_sq

theorem q8Biquad_fortyOne_dvd_discr :
    (41 : ℤ) ∣ NumberField.discr K2 :=
  prime_dvd_numberField_discr_of_integral_square 41 (by norm_num)
    q8BiquadFortyOneRoot q8BiquadFortyOneRoot_sq

/-- Exact rational-prime support of the maximal abelian subfield discriminant. -/
theorem q8Biquad_prime_dvd_discr_iff (p : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ NumberField.discr K2 ↔ p = 5 ∨ p = 41 := by
  constructor
  · exact q8Biquad_prime_dvd_discr_eq_five_or_fortyOne p hp
  · rintro (rfl | rfl)
    · exact q8Biquad_five_dvd_discr
    · exact q8Biquad_fortyOne_dvd_discr

end


end RHTower
