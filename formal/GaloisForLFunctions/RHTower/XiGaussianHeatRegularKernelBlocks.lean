import GaloisForLFunctions.RHTower.XiGaussianHeatRegularKernel

/-!
# Exact block Christoffel--Darboux decomposition for the heat source

Each complete singular gap contributes the divided difference of its
polynomial transfer quotient. Summing these contributions recovers the
actual inverse Hankel kernel, including indefinite sections. A scalar
rank-one term is replaced by the whole polynomial gap contribution.
-/

open Polynomial Matrix HTGeometry
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Full kernel contribution of one canonical normal block. -/
def heatRegularKernelBlock (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) : ℝ[X] :=
  ((heatRegularAdmission a j).eval x / heatRegularCoupling a j) •
    (heatRegularAdmission a j * momentDividedDifference (heatRegularQuotient a j) x)

theorem heatRegularQuotient_zero (a : {t : ℝ // 0 < t}) :
    heatRegularQuotient a 0 = heatRegularAdmission a 1 := by
  unfold heatRegularQuotient momentBlockQuotient
  rw [heatRegularHead_add_gap]
  change heatRegularAdmission a 1 /ₘ heatRegularAdmission a 0 = _
  rw [heatRegularAdmission_zero, divByMonic_one]

theorem heatRegularKernel_zero (a : {t : ℝ // 0 < t}) (x : ℝ) :
    heatRegularKernel a 0 x = heatRegularKernelBlock a 0 x := by
  simp [heatRegularKernel, heatRegularKernelBlock, heatRegularQuotient_zero,
    momentDividedDifference_one, one_div]

/-- Transfer adds exactly one complete block contribution. -/
theorem heatRegularKernel_step (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    heatRegularKernel a (j + 1) x =
      heatRegularKernel a j x + heatRegularKernelBlock a (j + 1) x := by
  have he : C ((heatRegularCoupling a (j + 1))⁻¹) * C (heatRegularEdge a j) =
      C ((heatRegularCoupling a j)⁻¹) := by
    rw [← C_mul]
    congr 1
    unfold heatRegularEdge
    rw [div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (heatRegularCoupling_ne_zero a (j + 1)), one_mul]
  simp only [heatRegularKernel, heatRegularKernelBlock,
    show j + 1 + 1 = j + 2 by omega, hcf_regular_head_recurrence a j,
    momentDividedDifference_sub_C_mul, momentDividedDifference_mul,
    eval_sub, eval_mul, eval_C, smul_eq_C_mul, div_eq_mul_inv, C_mul, C_sub]
  linear_combination
    (C ((heatRegularAdmission a j).eval x) *
        momentDividedDifference (heatRegularAdmission a (j + 1)) x -
      C ((heatRegularAdmission a (j + 1)).eval x) *
        momentDividedDifference (heatRegularAdmission a j) x) * he

/-- The gap quotients give the exact finite kernel at every regular head. -/
theorem hcf_regular_kernel_blocks (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    heatRegularKernel a j x =
      ∑ i ∈ Finset.range (j + 1), heatRegularKernelBlock a i x := by
  induction j with
  | zero => simpa using heatRegularKernel_zero a x
  | succ j ih => rw [heatRegularKernel_step, Finset.sum_range_succ, ih]

/-- The full inverse Hankel matrix is recovered from source polynomial
transfer across arbitrary singular gaps, without a sign premise. -/
theorem hcf_regular_inverse_kernel_blocks (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    ofFn (heatRegularHead a (j + 1))
        ((momentHankelMatrix (heatRealMoments a) (heatRegularHead a (j + 1)))⁻¹ *ᵥ
          fun i : Fin (heatRegularHead a (j + 1)) => x ^ (i : ℕ)) =
      ∑ i ∈ Finset.range (j + 1),
        ((heatRegularAdmission a i).eval x / heatRegularCoupling a i) •
          (heatRegularAdmission a i *
            momentDividedDifference (heatRegularQuotient a i) x) := by
  rw [← momentInverseKernel, ← hcf_regular_kernel_inverse, hcf_regular_kernel_blocks]
  rfl

/-- Block Christoffel--Darboux in division-free form, including the diagonal. -/
theorem hcf_regular_block_christoffel_darboux
    (a : {t : ℝ // 0 < t}) (j : ℕ) (x y : ℝ) :
    (y - x) *
        (∑ i ∈ Finset.range (j + 1), heatRegularKernelBlock a i x).eval y =
      ((heatRegularAdmission a j).eval x * (heatRegularAdmission a (j + 1)).eval y -
        (heatRegularAdmission a (j + 1)).eval x * (heatRegularAdmission a j).eval y) /
          heatRegularCoupling a j := by
  rw [← hcf_regular_kernel_blocks]
  have h := congrArg (Polynomial.eval y) (heatRegularKernel_displacement a j x)
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_smul, smul_eq_mul] at h
  rw [h]
  ring

end
end RHTower
