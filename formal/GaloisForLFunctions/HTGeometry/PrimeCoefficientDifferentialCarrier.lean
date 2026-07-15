import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField

/-!
# General prime-coefficient differential carrier

The prime-supported arithmetic column with coefficients `c p`, shifted by `a`, is placed directly
in the rational-coordinate differential field.  Its differential jets are the expected powers of
the rotated logarithmic clock.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

/-- The order-`k` rotated jet of an arbitrary prime coefficient column at shift `a`. -/
def primeCoefficientShiftedRotatedJet
    (c : Nat.Primes → ℂ) (a : ℂ) (k : ℕ) : ArithmeticFunction ℂ :=
  arithmeticOfPrimeColumn fun p =>
    c p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k

@[simp]
theorem rotatedLogFractionDerivation_primeCoefficientShiftedRotatedJet
    (c : Nat.Primes → ℂ) (a : ℂ) (k : ℕ) :
    rotatedLogFractionDerivation
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeCoefficientShiftedRotatedJet c a k)) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeCoefficientShiftedRotatedJet c a (k + 1)) := by
  rw [rotatedLogFractionDerivation_algebraMap]
  congr 1
  ext n
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, logWeight_apply]
  by_cases hn : n.Prime
  · rw [primeCoefficientShiftedRotatedJet,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩]
    simp only [rotatedPrimeLogClock, primeLogClock, pow_succ]
    ring
  · simp [primeCoefficientShiftedRotatedJet, arithmeticOfPrimeColumn, hn]

/-- The formal differential carrier of a general prime coefficient column. -/
def primeCoefficientShiftCarrier (c : Nat.Primes → ℂ) (a : ℂ) :
    arithmeticFunctionRationalCoordinateField :=
  algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
    (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primeCoefficientShiftedRotatedJet c a 0))

@[simp]
theorem differentialJet_primeCoefficientShiftCarrier
    (c : Nat.Primes → ℂ) (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k (primeCoefficientShiftCarrier c a) =
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeCoefficientShiftedRotatedJet c a k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih,
        arithmeticFunctionRationalCoordinateField_deriv_algebraMap,
        arithmeticFunctionFractionField_deriv_apply,
        rotatedLogFractionDerivation_primeCoefficientShiftedRotatedJet]

/-- The canonical complete natural-shift palette of one prime coefficient column. -/
def primeCoefficientNaturalShiftPalette
    (c : Nat.Primes → ℂ) (a : ℕ) : arithmeticFunctionRationalCoordinateField :=
  primeCoefficientShiftCarrier c (a : ℂ)

end


end GaloisForLFunctions.HTGeometry
