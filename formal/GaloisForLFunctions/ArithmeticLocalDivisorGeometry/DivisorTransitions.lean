import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.LocalFactors

/-!
# Exact coefficient transitions at central divisor points

Central zero factors shift coefficient indices. Positive scalar normalizations preserve every
coefficient sign. Both operations are reversible on the coefficient cone, including its boundary.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section

/-- Central multiplicity shifts coefficient indices without changing their signs. -/
theorem coeffNonneg_mul_X_pow_iff (p : ℝ[X]) (a : ℕ) :
    CoeffNonneg (p * X ^ a) ↔ CoeffNonneg p := by
  constructor
  · intro h n
    simpa only [coeff_mul_X_pow] using h (n + a)
  · intro h n
    rw [coeff_mul_X_pow']
    split_ifs
    · exact h _
    · exact le_rfl

theorem coeffNonneg_X_pow_mul_iff (p : ℝ[X]) (a : ℕ) :
    CoeffNonneg (X ^ a * p) ↔ CoeffNonneg p := by
  rw [mul_comm, coeffNonneg_mul_X_pow_iff]

/-- Positive scalar normalizations are harmless even when individual coefficients vanish. -/
theorem coeffNonneg_C_mul_iff (p : ℝ[X]) {c : ℝ} (hc : 0 < c) :
    CoeffNonneg (C c * p) ↔ CoeffNonneg p := by
  change (∀ n, 0 ≤ (C c * p).coeff n) ↔ ∀ n, 0 ≤ p.coeff n
  simp only [coeff_C_mul, mul_nonneg_iff_of_pos_left hc]

/-- A positive normalization and any central multiplicity can be removed together. -/
theorem coeffNonneg_positive_monomial_mul_iff (p : ℝ[X]) (a : ℕ) {c : ℝ} (hc : 0 < c) :
    CoeffNonneg ((C c * X ^ a) * p) ↔ CoeffNonneg p := by
  rw [mul_assoc, coeffNonneg_C_mul_iff _ hc, coeffNonneg_X_pow_mul_iff]

end

end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
