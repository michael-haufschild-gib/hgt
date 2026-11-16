import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginCharacterization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPlaceClassification

/-!
# Intrinsic characterization of the Kummer origin

Multiplication by a nonzero constant preserves membership in every
constant-field valuation ring. The reciprocal of the Kummer coordinate
fails to be integral at precisely the actual origin place. This statement
ranges over all constant-field places, including nonrational places.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis

/-- Nonzero constants act by units in every constant-field place. -/
theorem constantFieldPlace_constant_mul_mem_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ConstantFieldPlaces K L) (a : K) (ha : a ≠ 0) (f : L) :
    algebraMap K L a * f ∈ W.val ↔ f ∈ W.val := by
  constructor
  · intro hf
    have h : algebraMap K L a⁻¹ * (algebraMap K L a * f) ∈ W.val :=
      mul_mem (W.property.2 a⁻¹) hf
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul] at h
  · intro hf
    exact mul_mem (W.property.2 a) hf

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "b" => p ^ (d + 1) - 2
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c b R
local notation "y" => algebraMap K[X] L X
local notation "O" => squareKummerFiniteConstantPlace p s c d r
  (squareKummerOriginPlace p s c b R)

/-- Among all actual constant-field places, the reciprocal coordinate has a pole only at the origin. -/
theorem squareKummerConstantPlace_origin_iff_inverse_notMem (W : ConstantFieldPlaces K L) :
    W = O ↔ y⁻¹ ∉ W.val := by
  constructor
  · rintro rfl hx
    change squareKummerOriginValuation p s c b R y⁻¹ ≤ 1 at hx
    rw [map_inv₀, squareKummerOriginValuation_coordinate] at hx
    have hle := (inv_le_one₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)).mp hx
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hle
    have hpos : (0 : ℤ) < ((p ^ (s + 1) + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.succ_pos (p ^ (s + 1))
    omega
  · intro hx
    rcases squareKummer_constantPlace_cases p s c d r W with ⟨w, hw⟩ | hw
    · have he : w = squareKummerOriginPlace p s c b R := by
        by_contra hne
        apply hx
        rw [← hw]
        change w.valuation L y⁻¹ ≤ 1
        rw [map_inv₀, squareKummer_coordinate_valuation_one_of_ne_origin p s c b R w hne,
          inv_one]
      rw [← hw, he]
    · exfalso
      apply hx
      rw [← hw]
      change squareKummerInfinityValuation p s c d r y⁻¹ ≤ 1
      rw [map_inv₀, squareKummerInfinityValuation_coordinate]
      apply (inv_le_one₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)).mpr
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      exact_mod_cast Nat.zero_le (p ^ (s + 1) + 1)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
