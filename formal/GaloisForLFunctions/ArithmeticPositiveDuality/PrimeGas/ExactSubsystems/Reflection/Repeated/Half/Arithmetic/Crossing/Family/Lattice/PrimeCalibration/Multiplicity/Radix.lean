import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Counting
import Mathlib.Algebra.Polynomial.Expand

/-! # Coefficient height at an integer root of an occupation polynomial -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Polynomial Finset

/-- At a positive integer root above one, the lower digits must cancel
the leading coefficient. A finite geometric sum makes the bound strict. -/
theorem root_height (P : ℤ[X]) (nz : P ≠ 0) (b H : ℕ) (hb : 1 < b)
    (root : P.eval (b : ℤ) = 0) (cap : ∀ j, (P.coeff j).natAbs ≤ H) :
    (b-1)*P.leadingCoeff.natAbs < H := by
  let N := P.natDegree
  let x : ℤ := b
  have xpos : 0 < x := by dsimp [x]; omega
  have xone : 1 < x := by dsimp [x]; omega
  have lead : 0 < |P.leadingCoeff| := abs_pos.mpr (leadingCoeff_ne_zero.mpr nz)
  have equation : (∑ j ∈ range N, P.coeff j*x^j) + P.leadingCoeff*x^N = 0 := by
    simpa only [eval_eq_sum_range,sum_range_succ,coeff_natDegree,N,x] using root
  have norm : |P.leadingCoeff| * x^N ≤ (H : ℤ) * ∑ j ∈ range N, x^j := by
    calc
      _ = |-(P.leadingCoeff*x^N)| := by rw [abs_neg,abs_mul,abs_of_nonneg (pow_nonneg xpos.le _)]
      _ = |∑ j ∈ range N, P.coeff j*x^j| := by congr 1; linarith only [equation]
      _ ≤ ∑ j ∈ range N, |P.coeff j*x^j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range N, (H : ℤ)*x^j := by
        apply sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (pow_nonneg xpos.le _)]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg xpos.le _)
        simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr (cap j))
      _ = _ := (mul_sum _ _ _).symm
  have strict : (x-1)*|P.leadingCoeff| < H := by
    by_contra! bad
    have geom := geom_sum_mul x N
    have posSum : 0 ≤ ∑ j ∈ range N, x^j := sum_nonneg fun j _ => pow_nonneg xpos.le j
    have small := norm.trans (mul_le_mul_of_nonneg_right bad posSum)
    rw [show (x-1) * |P.leadingCoeff| * (∑ j ∈ range N, x^j) =
      |P.leadingCoeff| * ((∑ j ∈ range N, x^j)*(x-1)) by ring,geom] at small
    linarith only [small,lead]
  exact_mod_cast (show ((b-1 : ℕ) : ℤ)*(P.leadingCoeff.natAbs : ℤ)<H by
    simpa only [Nat.cast_sub (show 1 ≤ b from hb.le), Nat.cast_one,Int.natCast_natAbs,x] using strict)

#print axioms root_height

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
