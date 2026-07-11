import GaloisForLFunctions.DifferentialAlgebraicDeriv
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Derivative of an algebraic element over a non-derivation-closed base

Generalization of `isAlgebraic_deriv` to a base field `A` that need not be derivation-closed: if
`A` is a subfield over which every element has an algebraic derivative (`δ(A) ⊆ Aᵃˡᵍ`), then the
derivative of any element algebraic over `A` is again algebraic over `A`.  Differentiating the
minimal polynomial via `Derivation.apply_aeval_eq` expresses `z′` as a rational combination of `z`
and the derivatives of the (algebraic) coefficients, all of which lie in the integral closure of
`A`.  This is the jet-tower propagation step for the differential-transcendence matroid.
-/

open scoped Differential
open Polynomial

namespace GaloisForLFunctions

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]

/-- The value of `PolynomialModule.eval z (mapCoeffs (minpoly A z))` lies in the integral closure of
`A` in `K` when `z` and every coefficient derivative are integral over `A`. -/
theorem eval_mapCoeffs_mem_integralClosure (A : Subalgebra F K) {z : K}
    (hz : z ∈ integralClosure A K)
    (hcoeff : ∀ a : A, Differential.deriv (a : K) ∈ integralClosure A K)
    (p : A[X]) :
    PolynomialModule.eval z
        ((Differential.deriv.compAlgebraMap A).mapCoeffs p) ∈ integralClosure A K := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, PolynomialModule.eval_add]; exact add_mem hp hq
  | monomial n c =>
      rw [Derivation.mapCoeffs_monomial, PolynomialModule.eval_single]
      -- `= δ(c) • z^n`
      have hd : (Differential.deriv.compAlgebraMap A) c = Differential.deriv (c : K) := rfl
      rw [hd]
      exact Subalgebra.smul_mem _ (pow_mem hz n) (hcoeff c) |>.symm ▸
        (by exact Submodule.smul_mem _ _ (pow_mem hz n))

end GaloisForLFunctions
