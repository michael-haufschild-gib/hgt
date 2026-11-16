import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFinitePlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricTangentSupport
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationPrincipalDivisors

/-!
# Finite principal divisors of all geometric Hermitian tangents

The classification of finite primes transfers the complete contact formula
to the actual finitely supported valuation divisor. Its coefficients are
`-Q` at the point and `-1` at its square-Frobenius image; they add when the
two points coincide. Signs are opposite to zero orders.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s

/-- Every finite adic valuation is exactly the normalized valuation at its residue point. -/
theorem hermitianGeometricClosedPoint_valuation (w : HeightOneSpectrum B) :
    w.valuation H = hermitianGeometricPointValuation p s (hermitianGeometricClosedPoint p s w) := by
  exact (congrArg (fun v : HeightOneSpectrum B => v.valuation H)
    (hermitianGeometricPointPrime_closedPoint p s w)).symm.trans
      (hermitianGeometricPointPrime_valuation p s (hermitianGeometricClosedPoint p s w))

/-- The complete finite tangent divisor consists of the point and its Frobenius image. -/
theorem hermitianGeometricTangent_finiteValuationDivisor (P : HermitianAffinePoint p s E) :
    finiteValuationDivisor B H (hermitianGeometricTangentFunction p s P) =
      Finsupp.single (hermitianGeometricPointPrime p s P) (-(Q : ℤ)) +
        Finsupp.single (hermitianGeometricPointPrime p s (hermitianFrobeniusPoint p s E P)) (-1) := by
  classical
  ext w
  have hs (U : HermitianAffinePoint p s E) (m : ℤ) :
      (Finsupp.single (hermitianGeometricPointPrime p s U) m) w =
        if hermitianGeometricClosedPoint p s w = U then m else 0 := by
    by_cases h : hermitianGeometricClosedPoint p s w = U
    · have hw : w = hermitianGeometricPointPrime p s U := by
        rw [← h, hermitianGeometricPointPrime_closedPoint]
      rw [if_pos h, hw, Finsupp.single_eq_same]
    · have hw : w ≠ hermitianGeometricPointPrime p s U := by
        intro hw
        apply h
        rw [hw, hermitianGeometricClosedPoint_pointPrime]
      rw [if_neg h, Finsupp.single_eq_of_ne hw]
  rw [finiteValuationDivisor_apply, hermitianGeometricClosedPoint_valuation,
    hermitianGeometricPointValuation_tangent_all, WithZero.log_exp, Finsupp.add_apply, hs, hs]
  split_ifs <;> (simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_zero]; omega)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
