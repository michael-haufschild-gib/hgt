import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicDeriv
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Derivative of an algebraic element over a non-derivation-closed base

Generalization of `isAlgebraic_deriv` to a base field `A` that need not be derivation-closed: if
every element of `A` has a derivative that is again algebraic over `A` (`δ(A) ⊆ Aᵃˡᵍ`), then the
derivative of any element algebraic over `A` is again algebraic over `A`.  Differentiating the
minimal polynomial via `Derivation.apply_aeval_eq` writes `z′` as `-num / den`, where `num` is a
polynomial in `z` with coefficients among the derivatives of the (algebraic) minimal-polynomial
coefficients, and `den = m'(z) ≠ 0`.  Both lie in the integral closure of `A` in `K`, which is a
field, so `z′` does too.  This is the jet-tower propagation step for the differential-transcendence
matroid: it removes the derivation-closedness hypothesis of `isAlgebraic_deriv`.
-/

open Polynomial
open scoped Differential

namespace GaloisForLFunctions

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]

/-- If `z` and every coefficient derivative `δ(c)` are integral over the intermediate field `A`,
then `PolynomialModule.eval z ((δ|_A).mapCoeffs p)` is integral over `A`: it is a finite sum of
products `z ^ i · δ(pᵢ)` of integral elements. -/
theorem eval_mapCoeffs_mem_integralClosure (A : IntermediateField F K) {z : K}
    (hz : z ∈ integralClosure A K)
    (hcoeff : ∀ a : A, Differential.deriv (a : K) ∈ integralClosure A K)
    (p : A[X]) :
    (((Differential.deriv.compAlgebraMap A).mapCoeffs p).map K .id).eval z
      ∈ integralClosure A K := by
  rw [PolynomialModule.eval_apply, Finsupp.sum]
  refine sum_mem fun i _ => ?_
  change z ^ i * Differential.deriv (p.coeff i : K) ∈ integralClosure A K
  exact mul_mem (pow_mem hz i) (hcoeff (p.coeff i))

omit [Differential K] in
/-- A polynomial expression `aeval z q` in an element `z` integral over `A`, with coefficients in
`A`, is itself integral over `A`. -/
theorem aeval_mem_integralClosure (A : IntermediateField F K) {z : K}
    (hz : z ∈ integralClosure A K) (q : A[X]) :
    (aeval z) q ∈ integralClosure A K := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c =>
      rw [aeval_monomial]
      exact mul_mem (Subalgebra.algebraMap_mem _ c) (pow_mem hz n)

/-- **Jet-tower propagation.**  Over an intermediate field `A` on which the derivation maps every
element to something algebraic over `A`, the derivative of any element `z` algebraic over `A` is
again algebraic over `A` — with no derivation-closedness assumption on `A`. -/
theorem deriv_mem_integralClosure (A : IntermediateField F K) [CharZero K]
    (hcoeff : ∀ a : A, Differential.deriv (a : K) ∈ integralClosure A K)
    {z : K} (hz : z ∈ integralClosure A K) :
    Differential.deriv z ∈ integralClosure A K := by
  have hzint : IsIntegral A z := hz
  have hzalg : IsAlgebraic A z := hzint.isAlgebraic
  have haeval : (aeval z) (minpoly A z) = 0 := minpoly.aeval A z
  have hkey := Derivation.apply_aeval_eq Differential.deriv z (minpoly A z)
  rw [haeval, map_zero, smul_eq_mul] at hkey
  -- `hkey : 0 = num + den * z′`
  have hden_ne : (aeval z) (derivative (minpoly A z)) ≠ 0 :=
    aeval_derivative_minpoly_ne_zero hzalg
  have hnum_mem :
      (((Differential.deriv.compAlgebraMap A).mapCoeffs (minpoly A z)).map K .id).eval z
        ∈ integralClosure A K :=
    eval_mapCoeffs_mem_integralClosure A hz hcoeff (minpoly A z)
  have hden_mem : (aeval z) (derivative (minpoly A z)) ∈ integralClosure A K :=
    aeval_mem_integralClosure A hz _
  have hden_int : IsIntegral A ((aeval z) (derivative (minpoly A z))) := hden_mem
  have hsolve : Differential.deriv z =
      (-(((Differential.deriv.compAlgebraMap A).mapCoeffs (minpoly A z)).map K .id).eval z)
        * ((aeval z) (derivative (minpoly A z)))⁻¹ := by
    field_simp
    linear_combination -hkey
  rw [hsolve]
  exact mul_mem (neg_mem hnum_mem) (hden_int.inv_mem hden_mem)

end GaloisForLFunctions
