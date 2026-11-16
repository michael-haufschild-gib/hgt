import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionPlaceClassification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionFiniteCount

/-!
# Intrinsic rational-place counts over extended constants

Rational finite normalization primes and the unique infinity place
enumerate all intrinsic rational places without repetitions. The
punctured literal count therefore acquires exactly the three resolved
boundary contributions.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] (η : Eˣ)
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "a" => (q - 1) * R
local notation "c" => (η⁻¹) ^ a
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "δ" => Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1) R
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a
local notation "S" => RationalPolynomialPrimes E B

local instance intrinsicCountPolynomialTorsionFree : Module.IsTorsionFree E[X] L :=
  kummerBranchField_torsionFree c 0 a (M - 1)

local instance intrinsicCountNormalizationTorsionFree : Module.IsTorsionFree E[X] B :=
  inferInstanceAs (Module.IsTorsionFree E[X] (integralClosure E[X] L))

local instance intrinsicCountNormalizationAlgebra : Algebra B L :=
  inferInstanceAs (Algebra (integralClosure E[X] L) L)

local instance intrinsicCountNormalizationFractionRing : IsFractionRing B L :=
  primePowerThreePointExtensionNormalization_fractionRing p d n E c a

/-- An actual rational normalization prime defines its intrinsic rational valuation place. -/
def primePowerKummerExtensionRationalPrimeToPlace (P : S) : RationalConstantFieldPlaces E L :=
  polynomialNormalizationRationalFinitePlace (K := E) («L» := L)
    (rationalPolynomialPrimeHeightOneEquiv E B P).val
    (rationalPolynomialPrimeHeightOneEquiv E B P).property

/-- Distinct rational finite normalization primes remain distinct intrinsic places. -/
theorem primePowerKummerExtensionRationalPrimeToPlace_injective :
    Function.Injective (primePowerKummerExtensionRationalPrimeToPlace p d n r E η) := by
  intro P Q h
  have hw := polynomialNormalizationFiniteConstantPlace_injective (K := E) («L» := L)
    (congrArg Subtype.val h)
  exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal hw)

/-- A finite normalization place cannot equal the coordinate-pole place at infinity. -/
theorem primePowerKummerExtensionRationalPrimeToPlace_ne_infinity (P : S) :
    primePowerKummerExtensionRationalPrimeToPlace p d n r E η P ≠
      primePowerKummerExtensionRationalInfinityPlace p d n r E η := by
  intro h
  have hx := polynomialNormalizationFiniteConstantPlace_coordinate_mem (K := E) («L» := L)
    (rationalPolynomialPrimeHeightOneEquiv E B P).val
  change algebraMap E[X] L X ∈
    (primePowerKummerExtensionRationalPrimeToPlace p d n r E η P).val.val at hx
  rw [h] at hx
  exact primePowerKummerExtensionInfinity_coordinate_notMem p d n r E η hx

/-- Finite rational primes together with infinity enumerate intrinsic rational places. -/
def primePowerKummerExtensionRationalPlaceMap :
    (S ⊕ PUnit.{1}) → RationalConstantFieldPlaces E L :=
  Sum.elim (primePowerKummerExtensionRationalPrimeToPlace p d n r E η)
    (fun _ => primePowerKummerExtensionRationalInfinityPlace p d n r E η)

/-- The normalization enumeration contains no repeated intrinsic place. -/
theorem primePowerKummerExtensionRationalPlaceMap_injective :
    Function.Injective (primePowerKummerExtensionRationalPlaceMap p d n r E η) := by
  intro x y h
  cases x with
  | inl P =>
    cases y with
    | inl Q =>
      exact congrArg Sum.inl
        (primePowerKummerExtensionRationalPrimeToPlace_injective p d n r E η h)
    | inr u => exact (primePowerKummerExtensionRationalPrimeToPlace_ne_infinity p d n r E η P h).elim
  | inr u =>
    cases y with
    | inl Q => exact (primePowerKummerExtensionRationalPrimeToPlace_ne_infinity p d n r E η Q h.symm).elim
    | inr v => exact congrArg Sum.inr (Subsingleton.elim u v)

/-- Every intrinsic rational place occurs in the normalization enumeration. -/
theorem primePowerKummerExtensionRationalPlaceMap_surjective :
    Function.Surjective (primePowerKummerExtensionRationalPlaceMap p d n r E η) := by
  intro W
  rcases primePowerKummerExtension_rationalPlace_cases p d n r E η W with ⟨w, hw, hW⟩ | hW
  · let P : S := ⟨w.asIdeal, w.isPrime, hw⟩
    have he : (rationalPolynomialPrimeHeightOneEquiv E B P).val = w := HeightOneSpectrum.ext rfl
    refine ⟨Sum.inl P, ?_⟩
    apply Subtype.ext
    change polynomialNormalizationFiniteConstantPlace (K := E) («L» := L)
      (rationalPolynomialPrimeHeightOneEquiv E B P).val = W.val
    rw [he]
    exact congrArg Subtype.val hW
  · exact ⟨Sum.inr PUnit.unit, hW⟩

/-- The finite normalization primes and infinity classify intrinsic rational places bijectively. -/
def primePowerKummerExtensionRationalPlaceEquiv :
    (S ⊕ PUnit.{1}) ≃ RationalConstantFieldPlaces E L :=
  Equiv.ofBijective (primePowerKummerExtensionRationalPlaceMap p d n r E η)
    ⟨primePowerKummerExtensionRationalPlaceMap_injective p d n r E η,
      primePowerKummerExtensionRationalPlaceMap_surjective p d n r E η⟩

variable [Finite E]

/-- The actual intrinsic rational-place count is the finite rational-prime count plus one. -/
theorem primePowerKummerExtension_rationalPlaces_card_eq_finite :
    Nat.card (RationalConstantFieldPlaces E L) = Nat.card S + 1 := by
  rw [← Nat.card_congr (primePowerKummerExtensionRationalPlaceEquiv p d n r E η),
    Nat.card_sum, Nat.card_unique (α := PUnit.{1})]

/-- The actual intrinsic rational-place count equals the punctured literal count plus all three boundary fibers. -/
theorem primePowerKummerExtension_rationalPlaces_card_eq_punctured :
    Nat.card (RationalConstantFieldPlaces E L) =
      Nat.card (PuncturedKummerPoints (M - 1) a c) + 2 + (q - 1) * δ := by
  letI : Fintype E := Fintype.ofFinite E
  rw [primePowerKummerExtension_rationalPlaces_card_eq_finite,
    primePowerKummerExtension_finiteRationalPrimes_card]
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

