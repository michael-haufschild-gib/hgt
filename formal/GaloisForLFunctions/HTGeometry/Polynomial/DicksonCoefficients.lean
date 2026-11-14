import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic.LinearCombination

/-!
# The leading coefficients of normalized Chebyshev polynomials

The recurrence gives degree at most `n`, leading coefficient one in positive
degree, zero subleading coefficient, and coefficient `-n` two degrees below
the leading term. These formulas hold in every characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The normalized recurrence never creates terms above its index. -/
theorem dickson_natDegree_le (n : ℕ) : (dickson 1 (1 : R) n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [dickson_zero]
  | one => simp only [dickson_one, natDegree_X, le_refl]
  | more n h0 h1 =>
    rw [dickson_add_two, C_1, one_mul]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le).trans (by simp only [natDegree_X]; omega)
    · omega

/-- Every positive-degree normalized Chebyshev polynomial has leading coefficient one. -/
theorem dickson_coeff_top (n : ℕ) : (dickson 1 (1 : R) (n + 1)).coeff (n + 1) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, dickson_add_two, C_1, one_mul,
      coeff_sub, coeff_X_mul]
    rw [ih,
      coeff_eq_zero_of_natDegree_lt ((dickson_natDegree_le n).trans_lt (by omega)), sub_zero]

/-- The center of the roots is zero: the subleading coefficient vanishes. -/
theorem dickson_coeff_subleading (n : ℕ) : (dickson 1 (1 : R) (n + 1)).coeff n = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, dickson_add_two, C_1, one_mul,
      coeff_sub, coeff_X_mul]
    rw [ih,
      coeff_eq_zero_of_natDegree_lt ((dickson_natDegree_le n).trans_lt (by omega)), sub_self]

/-- The first nontrivial coefficient below the leading term is minus the degree. -/
theorem dickson_coeff_subleading_two (n : ℕ) :
    (dickson 1 (1 : R) (n + 2)).coeff n = -((n + 2 : ℕ) : R) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 1) + 2 by omega, dickson_add_two, C_1, one_mul,
      coeff_sub, coeff_X_mul]
    rw [show n + 1 + 1 = n + 2 by omega, ih, dickson_coeff_top]
    push_cast
    ring

omit [Nontrivial R] in
/-- Reflection acts on a normalized Chebyshev polynomial by its degree parity. -/
theorem dickson_comp_neg_X (n : ℕ) :
    (dickson 1 (1 : R) n).comp (-X) = C ((-1 : R) ^ n) * dickson 1 (1 : R) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [dickson_zero]
  | one => simp
  | more n h0 h1 =>
    rw [dickson_add_two]
    simp only [sub_comp, mul_comp, X_comp, h0, h1,
      C_1, one_mul, pow_succ, C_mul, C_neg, C_1]
    ring

end GaloisForLFunctions.HTGeometry
