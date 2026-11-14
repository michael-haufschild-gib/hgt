import GaloisForLFunctions.HTGeometry.MonicResiduePairing
import GaloisForLFunctions.HTGeometry.ResidueRootFamilyTransfer
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Trace elements retain branch contacts

On a component defined by `f`, the derivative of the complete equation `f g`
is `f' g`: the intrinsic different is multiplied by the other-branch contact.
For split power-series sheets, the order of the trace element is exactly the
sum of the pairwise contact orders, including infinite order at coincident
branches. This is the split monogenic case of the compensation mechanism in
Theorem 8.12 and Corollary 8.13 of Du,
*Arithmetic theta products and doubling at arbitrary level*.
-/

noncomputable section
open Polynomial Finset
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

variable {R : Type*} [CommRing R]

/-- Restricting the complete trace element to a branch retains every other factor. -/
theorem branch_derivative_mul (f g : R[X]) :
    AdjoinRoot.mk f (f * g).derivative =
      AdjoinRoot.mk f f.derivative * AdjoinRoot.mk f g := by
  rw [derivative_mul, map_add, map_mul, map_mul, AdjoinRoot.mk_self,
    zero_mul, add_zero]

/-- For arbitrary split sheets, residue duality identifies trace with the full derivative. -/
theorem split_residueEquiv_symm_trace {ι : Type*} [Fintype ι] (a : ι → R) :
    (monicResidueEquiv (monic_prod_of_monic univ (fun i => X - C (a i))
      (fun i _ => monic_X_sub_C (a i)))).symm
        (Algebra.trace R (AdjoinRoot (∏ i, (X - C (a i))))) =
      AdjoinRoot.mk (∏ i, (X - C (a i))) (∏ i, (X - C (a i))).derivative := by
  let f : R[X] := ∏ i, (X - C (a i))
  have hf : f.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))
  change (monicResidueEquiv hf).symm (Algebra.trace R (AdjoinRoot f)) =
    AdjoinRoot.mk f f.derivative
  apply (monicResidueEquiv hf).injective
  rw [LinearEquiv.apply_symm_apply]
  ext x
  change Algebra.trace R (AdjoinRoot f) x =
    monicResidue hf (AdjoinRoot.mk f f.derivative * x)
  rw [monic_trace_eq_residue_derivative hf, mul_comm]

/-- The ideal of the complete derivative is the product of the intrinsic and contact ideals. -/
theorem branch_derivative_ideal (f g : R[X]) :
    Ideal.span ({AdjoinRoot.mk f (f * g).derivative} : Set (AdjoinRoot f)) =
      Ideal.span {AdjoinRoot.mk f f.derivative} * Ideal.span {AdjoinRoot.mk f g} := by
  rw [branch_derivative_mul, Ideal.span_singleton_mul_span_singleton]

section PowerSeries
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The full different order is the sum of all branch-contact orders.
The equality uses extended natural numbers, so repeated branches need no exception. -/
theorem split_derivative_order (a : ι → PowerSeries K) (i : ι) :
    ((Polynomial.derivative (∏ j, (X - C (a j)))).eval (a i)).order =
      ∑ j ∈ univ.erase i, (a i - a j).order := by
  rw [eval_derivative_prod_X_sub_C]
  exact PowerSeries.order_prod _ _

/-- Adjoining another sheet adds its exact contact order to the derivative on each branch. -/
theorem split_derivative_mul_order (a : ι → PowerSeries K) (g : (PowerSeries K)[X])
    (i : ι) :
    ((Polynomial.derivative ((∏ j, (X - C (a j))) * g)).eval (a i)).order =
      (∑ j ∈ univ.erase i, (a i - a j).order) + (g.eval (a i)).order := by
  have hz : (∏ j, (X - C (a j))).eval (a i) = 0 := by
    rw [eval_prod]
    exact prod_eq_zero (mem_univ i) (by simp only [eval_sub, eval_X, eval_C, sub_self])
  rw [derivative_mul, eval_add, eval_mul, eval_mul, hz, zero_mul, add_zero,
    PowerSeries.order_mul, split_derivative_order]

end PowerSeries

#print axioms branch_derivative_mul
#print axioms split_residueEquiv_symm_trace
#print axioms branch_derivative_ideal
#print axioms split_derivative_order
#print axioms split_derivative_mul_order

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
