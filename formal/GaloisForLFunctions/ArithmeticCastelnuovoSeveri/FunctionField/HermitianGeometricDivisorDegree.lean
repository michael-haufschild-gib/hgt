import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFrobeniusDivisors
import Mathlib.Algebra.Module.BigOperators

/-!
# Geometric point divisors and their degree-zero parts

Every geometric residue field is the constant field, so the degree of a
point divisor is its coefficient sum. The tangent product for an invariant
divisor `D` has the literal divisor `(Q+1)D - (Q+1)deg(D)[infinity]`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "H" => HermitianGeometricField p s
local notation "Div" => HermitianGeometricPlaceDivisor p s

/-- The actual divisor of a geometric point, including the unique infinity point. -/
def hermitianGeometricPointDivisor : HermitianGeometricPoint p s → Div
  | none => (0, 1)
  | some P => (Finsupp.single (hermitianGeometricPointPrime p s P) 1, 0)

/-- A signed point sum as a divisor on the actual normalization primes and infinity. -/
def hermitianGeometricDivisorOfPoints (D : HermitianGeometricPoint p s →₀ ℤ) : Div :=
  D.sum fun P n => n • hermitianGeometricPointDivisor p s P

/-- Degree over the algebraically closed constant field is the signed coefficient sum. -/
def hermitianGeometricDivisorDegree (D : HermitianGeometricPoint p s →₀ ℤ) : ℤ :=
  D.sum fun _ n => n

/-- Each normalized point divisor is its actual point minus infinity. -/
theorem hermitianGeometricPointDifference_eq (P : HermitianGeometricPoint p s) :
    hermitianGeometricPointDifference p s P = hermitianGeometricPointDivisor p s P - (0, 1) := by
  cases P <;> simp [hermitianGeometricPointDifference, hermitianGeometricPointDivisor]

/-- The normalized signed sum is literally `D - deg(D)[infinity]`. -/
theorem hermitianGeometricDegreeZeroPart_eq (D : HermitianGeometricPoint p s →₀ ℤ) :
    hermitianGeometricDegreeZeroPart p s D = hermitianGeometricDivisorOfPoints p s D -
      hermitianGeometricDivisorDegree p s D • (0, 1) := by
  unfold hermitianGeometricDegreeZeroPart hermitianGeometricDivisorOfPoints
    hermitianGeometricDivisorDegree
  simp_rw [hermitianGeometricPointDifference_eq, smul_sub]
  unfold Finsupp.sum
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]

/-- The tangent product realizes the full degree-normalized Frobenius-invariant divisor relation. -/
theorem hermitianGeometricTangentProduct_divisor_degree
    (D : HermitianGeometricPoint p s →₀ ℤ) (hD : hermitianGeometricFrobeniusDivisor p s D = D) :
    hermitianGeometricZeroPoleDivisor p s (hermitianGeometricTangentProduct p s D : H) =
      ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDivisorOfPoints p s D -
        (((Q + 1 : ℕ) : ℤ) * hermitianGeometricDivisorDegree p s D) • (0, 1) := by
  rw [hermitianGeometricTangentProduct_divisor_of_frobenius_fixed p s D hD,
    hermitianGeometricDegreeZeroPart_eq, smul_sub, smul_smul]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
