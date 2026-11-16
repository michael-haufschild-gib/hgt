import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFiniteTangentDivisors
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPlaceClassification

/-!
# Complete principal divisors of geometric Hermitian tangents

Every constant-field place is a finite normalization prime or the unique
point at infinity. Using positive coefficients for zeros and negative
coefficients for poles, the actual tangent divisor is
`Q[P] + [Fr(P)] - (Q+1)[infinity]` for every geometric affine point.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s

/-- Divisors on all finite normalization primes together with the unique geometric infinity place. -/
abbrev HermitianGeometricPlaceDivisor := (HeightOneSpectrum B →₀ ℤ) × ℤ

/-- The principal divisor with zeros positive and poles negative; zero is assigned the zero divisor. -/
def hermitianGeometricZeroPoleDivisor (f : H) : HermitianGeometricPlaceDivisor p s :=
  (-finiteValuationDivisor B H f, -WithZero.log (hermitianGeometricInfinityValuation p s f))

/-- The complete actual tangent divisor has contact `Q` at the point, one Frobenius contact, and pole `Q+1`. -/
theorem hermitianGeometricTangent_zeroPoleDivisor (P : HermitianAffinePoint p s E) :
    hermitianGeometricZeroPoleDivisor p s (hermitianGeometricTangentFunction p s P) =
      (Finsupp.single (hermitianGeometricPointPrime p s P) (Q : ℤ) +
        Finsupp.single (hermitianGeometricPointPrime p s (hermitianFrobeniusPoint p s E P)) 1,
          -((Q + 1 : ℕ) : ℤ)) := by
  apply Prod.ext
  · change -finiteValuationDivisor B H (hermitianGeometricTangentFunction p s P) = _
    rw [hermitianGeometricTangent_finiteValuationDivisor]
    simp [add_comm]
  · change -WithZero.log (hermitianGeometricInfinityValuation p s
      (hermitianGeometricTangentFunction p s P)) = _
    rw [hermitianGeometricInfinityValuation_tangent, WithZero.log_exp]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
