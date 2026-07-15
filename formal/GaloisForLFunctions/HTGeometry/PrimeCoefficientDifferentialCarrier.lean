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

/-- Prime-supported shifted jets commute with finite complex linear combinations of their source
columns. -/
theorem primeCoefficientShiftedRotatedJet_linearCombination
    {B : Type*} [Fintype B]
    (c : B → Nat.Primes → ℂ) (z : B → ℂ) (a : ℂ) (k : ℕ) :
    primeCoefficientShiftedRotatedJet (fun p => ∑ b, z b * c b p) a k =
      ∑ b, algebraMap ℂ (ArithmeticFunction ℂ) (z b) *
        primeCoefficientShiftedRotatedJet (c b) a k := by
  classical
  simp_rw [← Algebra.smul_def]
  ext n
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f => f n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  rw [show (∑ b, z b • primeCoefficientShiftedRotatedJet (c b) a k) n =
      ∑ b, (z b • primeCoefficientShiftedRotatedJet (c b) a k) n by
    exact map_sum ev _ Finset.univ]
  by_cases hn : n.Prime
  · let p : Nat.Primes := ⟨n, hn⟩
    rw [show primeCoefficientShiftedRotatedJet
        (fun p => ∑ b, z b * c b p) a k n =
          (∑ b, z b * c b p) * primeShiftFactor a p *
            rotatedPrimeLogClock p ^ k by
      exact arithmeticOfPrimeColumn_apply_prime _ p]
    simp only [ArithmeticFunction.smul_map, smul_eq_mul]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [show primeCoefficientShiftedRotatedJet (c b) a k n =
        c b p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k by
      exact arithmeticOfPrimeColumn_apply_prime _ p]
    ring
  · simp [primeCoefficientShiftedRotatedJet, arithmeticOfPrimeColumn, hn,
      ArithmeticFunction.smul_map]

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
  · let p : Nat.Primes := ⟨n, hn⟩
    rw [show primeCoefficientShiftedRotatedJet c a k n =
        c p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k by
      exact arithmeticOfPrimeColumn_apply_prime _ p]
    rw [show primeCoefficientShiftedRotatedJet c a (k + 1) n =
        c p * primeShiftFactor a p * rotatedPrimeLogClock p ^ (k + 1) by
      exact arithmeticOfPrimeColumn_apply_prime _ p]
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

/-- The same finite complex linear-combination law holds at every shifted differential jet in the
rational-coordinate ambient field. -/
theorem differentialJet_primeCoefficientShiftCarrier_linearCombination
    {B : Type*} [Fintype B]
    (c : B → Nat.Primes → ℂ) (z : B → ℂ) (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (primeCoefficientShiftCarrier (fun p => ∑ b, z b * c b p) a) =
      ∑ b, algebraMap ℂ arithmeticFunctionRationalCoordinateField (z b) *
        GaloisForLFunctions.differentialJet k
          (primeCoefficientShiftCarrier (c b) a) := by
  classical
  simp_rw [differentialJet_primeCoefficientShiftCarrier]
  rw [primeCoefficientShiftedRotatedJet_linearCombination]
  rw [map_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [map_mul, map_mul]
  congr 1

/-- The canonical complete natural-shift palette of one prime coefficient column. -/
def primeCoefficientNaturalShiftPalette
    (c : Nat.Primes → ℂ) (a : ℕ) : arithmeticFunctionRationalCoordinateField :=
  primeCoefficientShiftCarrier c (a : ℂ)

end


end GaloisForLFunctions.HTGeometry
