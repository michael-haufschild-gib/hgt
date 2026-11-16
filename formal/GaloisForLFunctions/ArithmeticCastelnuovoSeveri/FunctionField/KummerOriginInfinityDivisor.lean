import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginCharacterization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDivisorClassFrobenius

/-!
# The origin-minus-infinity class of a Kummer cover

The original coordinate has its unique finite zero at the origin and
its unique pole at infinity, both of order Q+1. Its reciprocal therefore
exhibits `(Q+1)(origin-infinity)` as an actual principal valuation divisor.
The corresponding divisor class is killed by Q+1.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ)
local notation "s" => kummerSquareIndex d n
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "b" => p ^ (d + 1) - 2
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c b R
local notation "B" => SquareKummerNormalization p s c b R
local notation "y" => algebraMap K[X] L X
local notation "O" => squareKummerOriginPlace p s c b R

/-- The coordinate's complete principal valuation divisor has precisely the origin and infinity coefficients. -/
theorem primePowerKummerCoordinate_functionDivisor :
    primePowerKummerFunctionDivisor p d n r c y =
      (Finsupp.single O (-((Q + 1 : ℕ) : ℤ)), ((Q + 1 : ℕ) : ℤ)) := by
  apply Prod.ext
  · exact squareKummerCoordinate_finiteValuationDivisor p s c b R
  · change WithZero.log (squareKummerInfinityValuation p s c d r y) = _
    rw [squareKummerInfinityValuation_coordinate, WithZero.log_exp]

/-- The difference between the actual rational origin and infinity as a finite place divisor. -/
def primePowerKummerOriginInfinityDivisor : PrimePowerKummerPlaceDivisor p d n r c :=
  (Finsupp.single O 1, -1)

/-- Multiplication by Q+1 makes the origin-minus-infinity divisor principal in the actual field. -/
theorem primePowerKummerOriginInfinityDivisor_nsmul_mem :
    (Q + 1) • primePowerKummerOriginInfinityDivisor p d n r c ∈
      primePowerKummerPrincipalDivisors p d n r c := by
  classical
  have hy : y ≠ 0 := (map_ne_zero (squareKummerOriginValuation p s c b R)).mp (by
    rw [squareKummerOriginValuation_coordinate]
    exact WithZero.exp_ne_zero)
  refine ⟨y⁻¹, inv_ne_zero hy, ?_, ?_⟩
  · intro w
    change WithZero.log (w.valuation L y⁻¹) = (Q + 1) • (Finsupp.single O (1 : ℤ)) w
    rw [map_inv₀, WithZero.log_inv, ← finiteValuationDivisor_apply B L y w,
      squareKummerCoordinate_finiteValuationDivisor]
    by_cases hw : w = O
    · subst w
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      simp only [nsmul_eq_mul, mul_one, neg_neg]
    · rw [Finsupp.single_eq_of_ne hw, Finsupp.single_eq_of_ne hw]
      simp only [neg_zero, nsmul_zero]
  · change WithZero.log (squareKummerInfinityValuation p s c d r y⁻¹) =
      (Q + 1) • (-1 : ℤ)
    rw [map_inv₀, WithZero.log_inv, squareKummerInfinityValuation_coordinate,
      WithZero.log_exp, nsmul_eq_mul, mul_neg_one]

/-- The class of the actual rational origin minus infinity. -/
def primePowerKummerOriginInfinityClass : PrimePowerKummerPlaceDivisorClass p d n r c :=
  QuotientAddGroup.mk' (primePowerKummerPrincipalDivisors p d n r c)
    (primePowerKummerOriginInfinityDivisor p d n r c)

/-- The actual origin-minus-infinity class is killed by the Kummer degree Q+1. -/
theorem primePowerKummerOriginInfinityClass_nsmul :
    (Q + 1) • primePowerKummerOriginInfinityClass p d n r c = 0 := by
  rw [primePowerKummerOriginInfinityClass, ← map_nsmul]
  change (((Q + 1) • primePowerKummerOriginInfinityDivisor p d n r c :
    PrimePowerKummerPlaceDivisor p d n r c) : PrimePowerKummerPlaceDivisorClass p d n r c) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact primePowerKummerOriginInfinityDivisor_nsmul_mem p d n r c

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
