import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerValuationFrobeniusCriterion

/-!
# Frobenius saturation of actual principal divisors

If multiplying an integer-valued place divisor by a characteristic
power makes it principal, the original divisor is already principal.
The root is produced in the same function field by the valuation-order
criterion, and cancellation of its characteristic power identifies
every order. No Jacobian or divisor-class comparison is assumed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "b" => p ^ (d + 1) - 2
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c b R
local notation "B" => SquareKummerNormalization p s c b R

/-- Multiplication by any characteristic power preserves and reflects principality of the actual normalized place orders. -/
theorem primePowerKummer_principal_orders_frobenius_saturated
    (e : ℕ) (a : HeightOneSpectrum B → ℤ) (z : ℤ) :
    (∃ f : L, f ≠ 0 ∧
      (∀ v, WithZero.log (v.valuation L f) = (p : ℤ) ^ e * a v) ∧
      WithZero.log (squareKummerInfinityValuation p s c d r f) = (p : ℤ) ^ e * z) ↔
    (∃ f : L, f ≠ 0 ∧
      (∀ v, WithZero.log (v.valuation L f) = a v) ∧
      WithZero.log (squareKummerInfinityValuation p s c d r f) = z) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have he : (p : ℤ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp)
  constructor
  · rintro ⟨f, hf, hfinite, hinfty⟩
    obtain ⟨g, hg⟩ := (primePowerKummer_frobenius_pow_iff_valuation_orders p d n r c e f).mpr
      ⟨fun v => ⟨a v, hfinite v⟩, ⟨z, hinfty⟩⟩
    have hg0 : g ≠ 0 := by
      intro hzero
      apply hf
      rw [← hg, hzero, zero_pow (pow_ne_zero _ hp)]
    refine ⟨g, hg0, ?_, ?_⟩
    · intro v
      apply mul_left_cancel₀ he
      calc
        (p : ℤ) ^ e * WithZero.log (v.valuation L g) = WithZero.log (v.valuation L f) := by
          rw [← hg, map_pow, WithZero.log_pow, nsmul_eq_mul, Nat.cast_pow]
        _ = (p : ℤ) ^ e * a v := hfinite v
    · apply mul_left_cancel₀ he
      calc
        (p : ℤ) ^ e * WithZero.log (squareKummerInfinityValuation p s c d r g) =
            WithZero.log (squareKummerInfinityValuation p s c d r f) := by
          rw [← hg, map_pow, WithZero.log_pow, nsmul_eq_mul, Nat.cast_pow]
        _ = (p : ℤ) ^ e * z := hinfty
  · rintro ⟨f, hf, hfinite, hinfty⟩
    refine ⟨f ^ (p ^ e), pow_ne_zero _ hf, ?_, ?_⟩
    · intro v
      rw [map_pow, WithZero.log_pow, nsmul_eq_mul, Nat.cast_pow, hfinite]
    · rw [map_pow, WithZero.log_pow, nsmul_eq_mul, Nat.cast_pow, hinfty]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
