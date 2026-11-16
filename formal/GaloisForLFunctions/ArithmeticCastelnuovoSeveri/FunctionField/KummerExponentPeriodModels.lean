import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizedExponentReduction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizedPrimeFibers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentPeriod

/-!
# Periodic isomorphisms of normalized Kummer fields

Reduced geometric exponents repeat modulo `q^n+1` after length `2n`.
Absorbing the matching coefficient power into the radical identifies
the actual function fields over their fixed constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis

/-- Geometric branch length has period `2n` up to an explicit constant-field isomorphism. -/
def kummerGeometricExponentPeriodEquiv {K : Type*} [Field K]
    (η : Kˣ) (b q n r : ℕ) :
    KummerBranchField (η⁻¹ ^ kummerExponent q (r + 2 * n)) b
      (kummerExponent q (r + 2 * n)) (q ^ n) ≃ₐ[K]
    KummerBranchField (η⁻¹ ^ kummerExponent q r) b (kummerExponent q r) (q ^ n) := by
  let e₁ := kummerNormalizedExponentReductionEquiv (b := b)
    (R := kummerExponent q (r + 2 * n)) (n := q ^ n) η
  have e₁' :
      KummerBranchField (η⁻¹ ^ (kummerExponent q r % (q ^ n + 1))) b
        (kummerExponent q r % (q ^ n + 1)) (q ^ n) ≃ₐ[K]
      KummerBranchField (η⁻¹ ^ kummerExponent q (r + 2 * n)) b
        (kummerExponent q (r + 2 * n)) (q ^ n) := by
    rw [← kummerExponent_mod_period q n r]
    exact e₁
  exact e₁'.symm.trans (kummerNormalizedExponentReductionEquiv (b := b)
    (R := kummerExponent q r) (n := q ^ n) η)

/-- The normalized prime-power family is periodic in its index over the very same square constant field. -/
def normalizedKummerPeriodEquiv
    (p : ℕ) [Fact p.Prime] (d n r : ℕ) :
    NormalizedKummerField p (kummerSquareIndex d n) d (r + 2 * (n + 1))
      ≃ₐ[SquareConstantField p (kummerSquareIndex d n)]
    NormalizedKummerField p (kummerSquareIndex d n) d r := by
  have he : (p ^ (d + 1)) ^ (n + 1) = p ^ (kummerSquareIndex d n + 1) := by
    rw [kummerSquareIndex_succ, pow_mul]
  have hr : r + 2 * (n + 1) + 1 = r + 1 + 2 * (n + 1) := by omega
  change KummerBranchField
    ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^
      kummerExponent (p ^ (d + 1)) (r + 2 * (n + 1) + 1))
    (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 2 * (n + 1) + 1))
    (p ^ (kummerSquareIndex d n + 1)) ≃ₐ[SquareConstantField p (kummerSquareIndex d n)]
    KummerBranchField
      ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^
        kummerExponent (p ^ (d + 1)) (r + 1))
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))
      (p ^ (kummerSquareIndex d n + 1))
  rw [hr, ← he]
  exact kummerGeometricExponentPeriodEquiv (kummerTraceConstant p (kummerSquareIndex d n))
    (p ^ (d + 1) - 2) (p ^ (d + 1)) (n + 1) (r + 1)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
