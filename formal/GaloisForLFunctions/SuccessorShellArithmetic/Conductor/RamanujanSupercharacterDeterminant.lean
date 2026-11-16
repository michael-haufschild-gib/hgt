import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.DivisorJetReciprocity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The divisor supercharacter determinant

The Ramanujan table indexed by divisors of a positive modulus squares to the
modulus times the identity. Taking determinants gives the exact squared
determinant, hence invertibility of the whole divisor transform.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence
noncomputable section

/-- Divisor classes index the supercharacters of the cyclic residue ring. -/
abbrev RamanujanDivisorClass (M : ℕ+) := {d : ℕ // d ∈ (M : ℕ).divisors}

/-- The cyclic supercharacter table, with complementary-divisor representatives. -/
def ramanujanSupercharacterTable (M : ℕ+) :
    Matrix (RamanujanDivisorClass M) (RamanujanDivisorClass M) ℝ :=
  fun d k => ramanujanLagCoefficient d.val ((M : ℕ) / k.val)

/-- The cyclic supercharacter transform is an involution scaled by its modulus. -/
theorem ramanujanSupercharacterTable_sq (M : ℕ+) :
    ramanujanSupercharacterTable M * ramanujanSupercharacterTable M =
      ((M : ℕ) : ℝ) • (1 : Matrix (RamanujanDivisorClass M) _ ℝ) := by
  classical
  ext d k
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  change (∑ r : RamanujanDivisorClass M,
      ramanujanLagCoefficient d.val ((M : ℕ) / r.val) *
      ramanujanLagCoefficient r.val ((M : ℕ) / k.val)) = _
  rw [← Finset.sum_subtype (M : ℕ).divisors (fun _ => Iff.rfl)]
  rw [sum_divisors_ramanujan_reciprocal M.pos
    (Nat.dvd_of_mem_divisors d.property) (Nat.dvd_of_mem_divisors k.property)]
  by_cases h : d = k
  · subst k
    simp
  · have hv : d.val ≠ k.val := fun he => h (Subtype.ext he)
    simp [h, hv]

/-- The squared determinant is the modulus to the number of divisor classes. -/
theorem ramanujanSupercharacterTable_det_sq (M : ℕ+) :
    (ramanujanSupercharacterTable M).det ^ 2 =
      ((M : ℕ) : ℝ) ^ (M : ℕ).divisors.card := by
  have h := congrArg Matrix.det (ramanujanSupercharacterTable_sq M)
  simpa only [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_coe, pow_two] using h

/-- No divisor supercharacter is lost under the finite transform. -/
theorem ramanujanSupercharacterTable_det_ne_zero (M : ℕ+) :
    (ramanujanSupercharacterTable M).det ≠ 0 := by
  intro h
  have hp : ((M : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.pos.ne'
  have he := ramanujanSupercharacterTable_det_sq M
  rw [h, zero_pow (by omega : 2 ≠ 0)] at he
  exact (pow_ne_zero _ hp) he.symm

/-- The determinant has the exact absolute size prescribed by orthogonality. -/
theorem abs_ramanujanSupercharacterTable_det (M : ℕ+) :
    |(ramanujanSupercharacterTable M).det| =
      Real.sqrt (((M : ℕ) : ℝ) ^ (M : ℕ).divisors.card) := by
  rw [← ramanujanSupercharacterTable_det_sq, Real.sqrt_sq_eq_abs]

#print axioms ramanujanSupercharacterTable_sq
#print axioms ramanujanSupercharacterTable_det_sq
#print axioms ramanujanSupercharacterTable_det_ne_zero
#print axioms abs_ramanujanSupercharacterTable_det

end
end GaloisForLFunctions.SuccessorShellArithmetic
