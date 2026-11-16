import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators

/-!
# Reciprocal radical coordinates

If `(S+1)(T+1)=1+kN`, replacing `t` by `t⁻¹` and `z` by
`(1-t)^k/z^(T+1)` interchanges the two branch exponents. The same
integer identity recovers the old radical from its two known powers.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An explicit positive Bézout identity recovers an element from two powers in a subfield. -/
theorem intermediateField_mem_of_power_relation (E : IntermediateField K L)
    {z : L} (hz : z ≠ 0) {a b N k : ℕ} (h : a * b = 1 + k * N)
    (ha : z ^ a ∈ E) (hN : z ^ N ∈ E) : z ∈ E := by
  have hpow : (z ^ a) ^ b / (z ^ N) ^ k = z := by
    rw [← pow_mul, h, pow_add, pow_one, ← pow_mul, Nat.mul_comm N k,
      mul_div_cancel_right₀ _ (pow_ne_zero _ hz)]
  rw [← hpow]
  exact E.div_mem (pow_mem ha b) (pow_mem hN k)

/-- Inverting the rational coordinate exchanges complementary radical exponents. -/
theorem reciprocalRadical_pow {c t z : L} (hc : c ≠ 0) (ht : t ≠ 0)
    (hh : 1 - t ≠ 0) (N S T k : ℕ)
    (hrel : (S + 1) * (T + 1) = 1 + k * N)
    (heq : z ^ N = c * t * (1 - t) ^ S) :
    ((1 - t) ^ k / z ^ (T + 1)) ^ N =
      ((-1 : L) ^ T / c ^ (T + 1)) * t⁻¹ * (1 - t⁻¹) ^ T := by
  have hexp : k * N = S * (T + 1) + T := by nlinarith only [hrel]
  have hratio : 1 - t⁻¹ = -(1 - t) / t := by field_simp; ring
  have hleft : ((1 - t) ^ k / z ^ (T + 1)) ^ N =
      (1 - t) ^ T / (c ^ (T + 1) * t ^ (T + 1)) := by
    rw [div_pow, ← pow_mul (1 - t) k N, hexp, pow_add,
      ← pow_mul z (T + 1) N, Nat.mul_comm (T + 1) N, pow_mul z N (T + 1), heq,
      mul_pow, mul_pow, ← pow_mul (1 - t) S (T + 1)]
    field_simp [hc, ht, hh]
  have hsign : (-1 : L) ^ T * (-1 : L) ^ T = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [hleft, hratio, div_pow, neg_pow (1 - t) T]
  symm
  calc
    _ = ((-1 : L) ^ T * (-1 : L) ^ T) *
        (1 - t) ^ T / (c ^ (T + 1) * t ^ (T + 1)) := by
      rw [pow_succ t T]
      field_simp [hc, ht]
    _ = _ := by rw [hsign, one_mul]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
