import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityLatticeOfTheHorizon
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The arithmetic of Nair integrals in a polynomial ideal

Multiples of a fixed integer polynomial have rational moments with consecutive denominators.
Their integral lattice is governed by the gcd of these moments after multiplication by the
horizon period. Prime-power denominators isolate the leading coefficient from the lower terms.
-/

noncomputable section

open Polynomial Finset intervalIntegral

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The rational moment `∫₀¹ x^j Q(x) dx`, written without an analytic integral. -/
def nairRationalMoment (Q : ℤ[X]) (j : ℕ) : ℚ :=
  ∑ i ∈ range (Q.natDegree + 1), (Q.coeff i : ℚ) / (j + i + 1 : ℕ)

theorem nairIntegral_mul_X_pow (Q : ℤ[X]) (j : ℕ) :
    nairIntegral (Q * X ^ j) = (nairRationalMoment Q j : ℝ) := by
  have hexp : (fun x : ℝ => aeval x (Q * X ^ j)) =
      fun x => ∑ i ∈ range (Q.natDegree + 1), (Q.coeff i : ℝ) * x ^ (j + i) := by
    funext x
    rw [map_mul, map_pow, aeval_X, aeval_eq_sum_range]
    simp only [zsmul_eq_mul, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← pow_add, Nat.add_comm]
  unfold nairIntegral
  rw [hexp, integral_finsetSum (f := fun i x => (Q.coeff i : ℝ) * x ^ (j + i))
    fun i _ => (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _]
  unfold nairRationalMoment
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_pow]
  norm_num [div_eq_mul_inv, add_assoc]

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
