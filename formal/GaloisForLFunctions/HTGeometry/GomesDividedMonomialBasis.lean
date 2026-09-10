import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Divided monomials as the backward-shift basis for differentiation

The basis `X^n/n!` makes differentiation the backward shift. It is constructed by
rescaling the existing monomial basis, uniformly for characteristic-zero fields.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- The divided monomial basis of polynomials over a characteristic-zero field. -/
def gomesDividedMonomialBasis : Module.Basis ℕ K K[X] :=
  (Polynomial.basisMonomials K).unitsSMul fun n =>
    (Units.mk0 (n.factorial : K) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))⁻¹

/-- The rescaled basis has the exact divided-monomial formula. -/
theorem gomesDividedMonomialBasis_apply (n : ℕ) :
    gomesDividedMonomialBasis K n = (n.factorial : K)⁻¹ • (X ^ n : K[X]) := by
  simp only [gomesDividedMonomialBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, Polynomial.coe_basisMonomials,
    ← C_mul_X_pow_eq_monomial, map_one, one_mul]

/-- The zeroth divided monomial is the constant polynomial one. -/
theorem gomesDividedMonomialBasis_zero : gomesDividedMonomialBasis K 0 = 1 := by
  simp [gomesDividedMonomialBasis_apply]

/-- The constant coefficient selects exactly the zeroth divided monomial. -/
theorem gomesDividedMonomialBasis_coeff_zero (n : ℕ) :
    (gomesDividedMonomialBasis K n).coeff 0 = if n = 0 then 1 else 0 := by
  rw [gomesDividedMonomialBasis_apply, coeff_smul, coeff_X_pow]
  by_cases h : n = 0
  · subst n
    simp
  · simp [h, Ne.symm h]

/-- Differentiation kills the bottom of the divided-monomial chain. -/
theorem gomesDividedMonomialBasis_derivative_zero :
    (gomesDividedMonomialBasis K 0).derivative = 0 := by
  rw [gomesDividedMonomialBasis_zero, derivative_one]

/-- Differentiation lowers the divided-monomial index by one with no scalar factor. -/
theorem gomesDividedMonomialBasis_derivative_succ (n : ℕ) :
    (gomesDividedMonomialBasis K (n + 1)).derivative = gomesDividedMonomialBasis K n := by
  rw [gomesDividedMonomialBasis_apply, gomesDividedMonomialBasis_apply, map_smul,
    derivative_X_pow_succ, ← smul_eq_C_mul, smul_smul]
  congr 1
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [← Nat.cast_add_one, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hn, mul_one]

/-- A polynomial is determined by its derivative and its constant coefficient. -/
theorem gomesPolynomial_derivative_coeff_zero_iff (P Q : K[X]) :
    (P.derivative = Q.derivative ∧ P.coeff 0 = Q.coeff 0) ↔ P = Q := by
  constructor
  · rintro ⟨hd, h0⟩
    have hz : (P - Q).derivative = 0 := by rw [map_sub, hd, sub_self]
    have hc := eq_C_of_derivative_eq_zero hz
    rw [coeff_sub, h0, sub_self, map_zero] at hc
    exact sub_eq_zero.mp hc
  · rintro rfl
    exact ⟨rfl, rfl⟩

end GaloisForLFunctions.HTGeometry
