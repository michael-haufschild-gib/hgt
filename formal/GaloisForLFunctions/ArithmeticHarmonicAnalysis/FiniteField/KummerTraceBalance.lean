import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials

/-!
# Frobenius balance for geometric exponents

For the geometric exponent `R=(q^r-1)/(q-1)`, complementary parameters
`u` and `1-u` turn the weighted branch factors into `1-a^(q-1)`.
This identity recovers the scalar root of unity in a trace parameterization.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p]

omit [CharP A p] in
/-- Multiplication by the parameter completes the geometric exponent to a Frobenius power. -/
theorem kummerExponent_power_mul (d r : ℕ) (u : A) :
    u * (u ^ kummerExponent (p ^ (d + 1)) (r + 1)) ^ (p ^ (d + 1) - 1) =
      u ^ (p ^ (d + 1)) ^ (r + 1) := by
  have h := kummerExponent_mul_add (p ^ (d + 1) - 1) (r + 1)
  rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)] at h
  rw [← pow_mul, mul_comm u, ← pow_succ, h]

/-- Complementary trace parameters force the scalar's root-of-unity equation. -/
theorem kummer_trace_balance (d r : ℕ) (a u : A) :
    u * (1 - (a * u ^ kummerExponent (p ^ (d + 1)) (r + 1)) ^ (p ^ (d + 1) - 1)) +
      (1 - u) * (1 - (a * (1 - u) ^ kummerExponent (p ^ (d + 1)) (r + 1)) ^
        (p ^ (d + 1) - 1)) = 1 - a ^ (p ^ (d + 1) - 1) := by
  have hf : (1 - u) ^ (p ^ (d + 1)) ^ (r + 1) =
      1 - u ^ (p ^ (d + 1)) ^ (r + 1) := by
    simpa only [one_pow, pow_mul p] using
      sub_pow_char_pow (1 : A) u ((d + 1) * (r + 1))
  calc
    _ = 1 - a ^ (p ^ (d + 1) - 1) *
        (u * (u ^ kummerExponent (p ^ (d + 1)) (r + 1)) ^ (p ^ (d + 1) - 1) +
          (1 - u) * ((1 - u) ^ kummerExponent (p ^ (d + 1)) (r + 1)) ^ (p ^ (d + 1) - 1)) := by
      rw [mul_pow, mul_pow]
      ring
    _ = _ := by
      rw [kummerExponent_power_mul p d r u, kummerExponent_power_mul p d r (1 - u), hf]
      ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
