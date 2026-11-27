import GaloisForLFunctions.HilbertMetric.Kernels.SparsePowerSeriesMinors

/-! # Thermal response of a centered pair of opposite levels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Schedule

open Finset Real Set Matrix

variable {q : ℕ}

/-- Subtracting the compensator's response removes the constant Taylor coefficient.
All remaining even coefficients stay strictly positive. -/
theorem cosh_sub_one_det (t x : Fin q ↪o Ioi (0 : ℝ)) :
    0<(Matrix.of fun j i => cosh ((t j).val*(x i).val)-1).det := by
  let e := OrderEmbedding.ofStrictMono (fun m : ℕ => 2*(m+1)) (by intro i j h; dsimp only; omega)
  let a (m : ℕ) : Ioi (0 : ℝ) := ⟨((2*(m+1)).factorial : ℝ)⁻¹,show (0 : ℝ) < _ by positivity⟩
  refine HilbertMetric.sparseSeriesKernel_det_pos e a (fun z => cosh z-1) ?_ t x
  intro z _
  have tail := (hasSum_nat_add_iff' (f := fun m => z^(2*m)/((2*m).factorial : ℝ)) 1).mpr (Real.hasSum_cosh z)
  simpa only [e,a,OrderEmbedding.coe_ofStrictMono,Finset.sum_range_one,mul_zero,pow_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,div_eq_inv_mul,inv_one,one_mul] using tail

/-- Arbitrary first-order signed readings can be assigned at arbitrary distinct positive
temperatures by moving the pairs in a suitable direction. -/
theorem choose_velocity (t x : Fin q ↪o Ioi (0 : ℝ)) (b : Fin q → ℝ) :
    ∃ v : Fin q → ℝ, ∀ j, 4*(t j).val*(∑ i, (cosh ((t j).val*(x i).val)-1)*v i)=b j := by
  let M := Matrix.of fun j i => cosh ((t j).val*(x i).val)-1
  let w := fun j => b j/(4*(t j).val)
  have unit : IsUnit M.det := isUnit_iff_ne_zero.mpr (cosh_sub_one_det t x).ne'
  refine ⟨(M⁻¹).mulVec w,fun j => ?_⟩
  have id : M.mulVec ((M⁻¹).mulVec w)=w := by rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv M unit,Matrix.one_mulVec]
  have row := congrFun id j
  change (∑ i, (cosh ((t j).val*(x i).val)-1)*((M⁻¹).mulVec w i))=w j at row
  rw [row]
  unfold w
  field_simp [(show (0 : ℝ)<(t j).val from (t j).property).ne']

#print axioms cosh_sub_one_det
#print axioms choose_velocity

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Schedule
