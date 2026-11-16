import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricInversion
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricTangents
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTranslations

/-!
# The geometric Hermitian valuation at infinity

Coordinate inversion transports the normalized origin valuation to
infinity. The additive and radical coordinates have pole orders `Q+1`
and `Q`. Hence every geometric tangent has pole order `Q+1` there.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "u" => hermitianExtensionAdditiveCoordinate p s E
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "O" => hermitianAffineOrigin p s E
local notation "V₀" => hermitianGeometricPointValuation p s O
local notation "φ" => algebraMap E H

private theorem origin_radical : V₀ z = WithZero.exp (-1 : ℤ) := by
  simpa only [hermitianAffineOrigin, map_zero, sub_zero] using
    hermitianGeometricPointValuation_radical_sub p s O

private theorem origin_additive : V₀ u = WithZero.exp (-((Q + 1 : ℕ) : ℤ)) := by
  have hQ : Q ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hfix : (O).val.1 ^ (Q * Q) = (O).val.1 := by
    change (0 : E) ^ (Q * Q) = 0
    exact zero_pow (mul_ne_zero hQ hQ)
  have ht : hermitianGeometricTangentFunction p s O = u := by
    rw [hermitianGeometricTangentFunction_eq]
    change u - φ 0 - φ ((0 : E) ^ Q) * (z - φ 0) = u
    simp only [zero_pow hQ, map_zero, sub_zero, zero_mul]
  have h := hermitianGeometricPointValuation_tangent p s O
  rw [if_pos hfix, ht] at h
  exact h

/-- The actual normalized geometric infinity valuation obtained by coordinate inversion. -/
def hermitianGeometricInfinityValuation : Valuation H (WithZero (Multiplicative ℤ)) :=
  (V₀).comap (hermitianGeometricInversionHom p s).toRingHom

local notation "V" => hermitianGeometricInfinityValuation p s

/-- The infinity valuation has the full normalized discrete value group. -/
theorem hermitianGeometricInfinityValuation_surjective : Function.Surjective V :=
  (hermitianGeometricPointValuation_surjective p s O).comp
    (hermitianGeometricInversionHom_surjective p s)

/-- Every nonzero geometric constant is a unit at infinity. -/
theorem hermitianGeometricInfinityValuation_constant (a : E) (ha : a ≠ 0) : V (φ a) = 1 := by
  change V₀ (hermitianGeometricInversionHom p s (φ a)) = 1
  rw [AlgHom.commutes]
  exact hermitianGeometricPointValuation_constant p s O a ha

/-- The additive coordinate has pole order `Q+1` at geometric infinity. -/
theorem hermitianGeometricInfinityValuation_additive : V u = WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
  change V₀ (hermitianGeometricInversionHom p s u) = _
  rw [hermitianGeometricInversionHom_additive, map_inv₀, origin_additive,
    ← WithZero.exp_neg, neg_neg]

/-- The radical coordinate has pole order `Q` at geometric infinity. -/
theorem hermitianGeometricInfinityValuation_radical : V z = WithZero.exp ((Q : ℕ) : ℤ) := by
  change V₀ (hermitianGeometricInversionHom p s z) = _
  rw [hermitianGeometricInversionHom_radical, map_div₀, origin_radical, origin_additive,
    ← WithZero.exp_sub]
  congr 1
  omega

/-- Every geometric tangent has pole order `Q+1` at the actual infinity valuation. -/
theorem hermitianGeometricInfinityValuation_tangent (P : HermitianAffinePoint p s E) :
    V (hermitianGeometricTangentFunction p s P) = WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
  have hc (a : E) : V (φ a) ≤ 1 := by
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero]
      exact zero_le_one
    · rw [hermitianGeometricInfinityValuation_constant p s a ha]
  have hQ : (0 : ℤ) < (Q : ℕ) := by
    exact_mod_cast pow_pos (Fact.out : p.Prime).pos (s + 1)
  have h1 : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu : V (u - φ P.val.2) = WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
    have hlt : V (φ P.val.2) < V u := by
      rw [hermitianGeometricInfinityValuation_additive]
      exact lt_of_le_of_lt (hc P.val.2) h1
    rw [(V).map_sub_eq_of_lt_left hlt, hermitianGeometricInfinityValuation_additive]
  have htail : V ((φ P.val.1) ^ Q * (z - φ P.val.1)) <
      WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
    by_cases ha : P.val.1 = 0
    · simp only [ha, map_zero, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), zero_mul]
      exact zero_lt_iff.mpr WithZero.exp_ne_zero
    · rw [map_mul, map_pow, hermitianGeometricInfinityValuation_constant p s _ ha,
        one_pow, one_mul]
      have hlt : V (φ P.val.1) < V z := by
        rw [hermitianGeometricInfinityValuation_constant p s _ ha,
          hermitianGeometricInfinityValuation_radical, ← WithZero.exp_zero, WithZero.exp_lt_exp]
        exact hQ
      rw [(V).map_sub_eq_of_lt_left hlt, hermitianGeometricInfinityValuation_radical,
        WithZero.exp_lt_exp]
      omega
  rw [hermitianGeometricTangentFunction_eq, map_pow]
  rw [(V).map_sub_eq_of_lt_left (by rw [hu]; exact htail), hu]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
