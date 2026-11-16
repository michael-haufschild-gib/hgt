import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CyclicOperatorHom
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Cyclic modules in polynomial differential representations

The equation Dⁿf=0 cuts out exactly the polynomials of degree below n
in characteristic zero. Evaluation at the cyclic generator therefore
identifies Hom(K[X]/Xⁿ, K[t] with X acting as D) with this degree space.
The target is infinite-dimensional, but every cyclic Hom space is finite.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The differential kernel is the actual degree filtration, including n=0. -/
theorem ker_polynomialDerivative_pow (n : ℕ) :
    LinearMap.ker ((derivative : Module.End K K[X]) ^ n) = degreeLT K n := by
  ext f
  rw [LinearMap.mem_ker, Module.End.pow_apply, mem_degreeLT]
  constructor
  · intro h
    rw [degree_lt_iff_coeff_zero]
    intro j hj
    have hc := congrArg (fun q : K[X] => q.coeff (j - n)) h
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hj, coeff_zero, nsmul_eq_mul] at hc
    have hn : (j.descFactorial n : K) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hj))
    exact (mul_eq_zero.mp hc).resolve_left hn
  · exact iterate_derivative_eq_zero_of_degree_lt

/-- Cyclic differential maps are parametrized by their first n polynomial coefficients. -/
def cyclicDifferentialHomEquiv (n : ℕ) :
    CyclicOperatorHom (derivative : Module.End K K[X]) (X ^ n) ≃ₗ[K] (Fin n → K) :=
  (cyclicOperatorHomEquiv derivative (X ^ n)).trans
    ((LinearEquiv.ofEq _ _ (by
      rw [map_pow, aeval_X, ker_polynomialDerivative_pow])).trans (degreeLTEquiv K n))

/-- Exact finite dimension inside the infinite-dimensional differential representation. -/
theorem finrank_cyclicDifferentialHom (n : ℕ) :
    Module.finrank K (CyclicOperatorHom (derivative : Module.End K K[X]) (X ^ n)) = n := by
  rw [(cyclicDifferentialHomEquiv (K := K) n).finrank_eq]
  simp

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.ker_polynomialDerivative_pow
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.cyclicDifferentialHomEquiv
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.finrank_cyclicDifferentialHom

