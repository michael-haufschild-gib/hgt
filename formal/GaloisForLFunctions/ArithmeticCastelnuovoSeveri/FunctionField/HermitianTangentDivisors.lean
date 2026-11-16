import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTangentSupport
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianRationalPlaceOrbits
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.NormalizedValuationUniqueness
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDivisorClassFrobenius

/-!
# Actual principal divisors of rational Hermitian tangents

Each rational affine point gives a height-one prime of the actual
normalization. Uniqueness of surjective integer-valued valuations
identifies its normalized valuation with the transported origin
valuation. The tangent therefore has complete principal divisor
`(Q+1)(P-infinity)`, with the opposite sign in valuation-log convention.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s
local notation "H" => HermitianKummerField p s
local notation "B" => SquareKummerNormalization p s η⁻¹ (Q - 2) 1
local notation "HK" => HermitianAffinePoint p s K

local instance hermitianTangentNormalizationAlgebra : Algebra B H :=
  inferInstanceAs (Algebra (integralClosure K[X] H) H)

local instance hermitianTangentNormalizationFractionRing : IsFractionRing B H :=
  squareKummerNormalization_fractionRing p s η⁻¹ (Q - 2) 1

/-- Every rational affine point is represented by a finite height-one normalization prime. -/
theorem hermitianPointHeightOne_exists (P : HK) :
    ∃ w : HeightOneSpectrum B, squareKummerFiniteConstantPlace p s η⁻¹ s 1 w =
      (hermitianPointRationalPlace p s P).val := by
  rcases squareKummer_constantPlace_cases p s η⁻¹ s 1 (hermitianPointRationalPlace p s P).val with
    hfinite | hinfty
  · exact hfinite
  · exfalso
    apply hermitianPointRationalPlace_ne_infinity p s P
    exact Subtype.ext hinfty.symm

/-- The actual finite normalization prime corresponding to a rational affine Hermitian point. -/
def hermitianPointHeightOne (P : HK) : HeightOneSpectrum B :=
  (hermitianPointHeightOne_exists p s P).choose

/-- The chosen normalization prime gives exactly the transported rational place. -/
theorem hermitianPointHeightOne_place_eq (P : HK) :
    squareKummerFiniteConstantPlace p s η⁻¹ s 1 (hermitianPointHeightOne p s P) =
      (hermitianPointRationalPlace p s P).val :=
  (hermitianPointHeightOne_exists p s P).choose_spec

/-- Normalization fixes the scale: the adic and transported point valuations are exactly equal. -/
theorem hermitianPointHeightOne_valuation (P : HK) :
    (hermitianPointHeightOne p s P).valuation H = hermitianPointValuation p s P := by
  apply normalizedValuation_eq_of_valuationSubring_eq
    ((hermitianPointHeightOne p s P).valuation H) (hermitianPointValuation p s P)
  · exact (congrArg Subtype.val (hermitianPointHeightOne_place_eq p s P)).trans
      (hermitianPointRationalPlace_valuationSubring p s P)
  · exact HeightOneSpectrum.valuation_surjective H (hermitianPointHeightOne p s P)
  · exact (HeightOneSpectrum.valuation_surjective H
      (squareKummerOriginPlace p s η⁻¹ (Q - 2) 1)).comp
      (hermitianTranslationFieldAut p s P).surjective

/-- Distinct rational affine points give distinct height-one normalization primes. -/
theorem hermitianPointHeightOne_injective : Function.Injective (hermitianPointHeightOne p s) := by
  intro P U h
  apply hermitianPointRationalPlace_injective p s
  apply Subtype.ext
  rw [← hermitianPointHeightOne_place_eq p s P, ← hermitianPointHeightOne_place_eq p s U, h]

/-- A rational tangent has value one at every other finite normalization prime. -/
theorem hermitianTangent_valuation_one_of_ne (P : HK) (w : HeightOneSpectrum B)
    (hw : w ≠ hermitianPointHeightOne p s P) :
    w.valuation H (hermitianTangentFunction p s P) = 1 := by
  let W := squareKummerFiniteConstantPlace p s η⁻¹ s 1 w
  have ht : w.valuation H (hermitianTangentFunction p s P) ≤ 1 :=
    hermitianFinitePlace_tangent_mem p s P w
  have hi : (hermitianTangentFunction p s P)⁻¹ ∈ W.val := by
    by_contra hnot
    have he := (hermitianPointConstantPlace_iff_tangent_inverse_notMem p s P W).mpr hnot
    exact hw (squareKummerFiniteConstantPlace_injective p s η⁻¹ s 1
      (he.trans (hermitianPointHeightOne_place_eq p s P).symm))
  change w.valuation H (hermitianTangentFunction p s P)⁻¹ ≤ 1 at hi
  rw [map_inv₀] at hi
  exact le_antisymm ht ((inv_le_one₀ (zero_lt_iff.mpr
    ((map_ne_zero (w.valuation H)).mpr (hermitianTangentFunction_ne_zero p s P)))).mp hi)

/-- The finite principal valuation divisor of a rational tangent is exactly its point with multiplicity Q+1. -/
theorem hermitianTangent_finiteValuationDivisor (P : HK) :
    finiteValuationDivisor B H (hermitianTangentFunction p s P) =
      Finsupp.single (hermitianPointHeightOne p s P) (-((Q + 1 : ℕ) : ℤ)) := by
  classical
  ext w
  rw [finiteValuationDivisor_apply]
  by_cases hw : w = hermitianPointHeightOne p s P
  · subst w
    rw [Finsupp.single_eq_same, hermitianPointHeightOne_valuation p s P,
      hermitianPointValuation_tangent p s P, WithZero.log_exp]
  · rw [Finsupp.single_eq_of_ne hw, hermitianTangent_valuation_one_of_ne p s P w hw,
      WithZero.log_one]

/-- The complete actual tangent divisor is `(Q+1)(infinity-P)` in valuation-log convention. -/
theorem hermitianTangent_functionDivisor (P : HK) :
    primePowerKummerFunctionDivisor p s 0 1 η⁻¹ (hermitianTangentFunction p s P) =
      (Finsupp.single (hermitianPointHeightOne p s P) (-((Q + 1 : ℕ) : ℤ)),
        ((Q + 1 : ℕ) : ℤ)) := by
  apply Prod.ext
  · exact hermitianTangent_finiteValuationDivisor p s P
  · change WithZero.log (hermitianInfinityValuation p s (hermitianTangentFunction p s P)) = _
    rw [hermitianInfinityValuation_tangent, WithZero.log_exp]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
