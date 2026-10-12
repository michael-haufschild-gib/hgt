import GaloisForLFunctions.RHTower.PaperThetaDerivativeConvolution
import GaloisForLFunctions.HTGeometry.PaperDirichletL1Pairing

/-! # The actual closed quantile derivative as whole-line L¹ data

Zero extension places the derivative in the existing real-line translation
space while preserving its exact pairing with every Dirichlet primitive.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

def closedQuantileDerivative (z : ℂ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (deriv (closedQuantileMode z))

theorem integrable_closedQuantileDerivative (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    Integrable (closedQuantileDerivative z.val) := by
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (intervalIntegrable_deriv_closedQuantileMode z).1

def closedQuantileDerivativeL1 (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    Lp ℂ 1 (volume : Measure ℝ) :=
  (integrable_closedQuantileDerivative z).toL1 (closedQuantileDerivative z.val)

theorem closedQuantileDerivativeL1_ae (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    (closedQuantileDerivativeL1 z : ℝ → ℂ) =ᵐ[volume] closedQuantileDerivative z.val :=
  (integrable_closedQuantileDerivative z).coeFn_toL1

theorem derivative_convolution_eq_L1 (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (N : ℕ) (t : ℝ) :
    (∫ y in (0 : ℝ)..1,
      deriv (closedQuantileMode z.val) y * Period.meanZeroDirichletPrimitive N (t - y)) =
      Period.dirichletPrimitiveConvolution N (closedQuantileDerivativeL1 z) t := by
  unfold Period.dirichletPrimitiveConvolution
  have he : (fun y => closedQuantileDerivative z.val y * Period.meanZeroDirichletPrimitive N (t - y)) =
      (Ioc (0 : ℝ) 1).indicator (fun y =>
        deriv (closedQuantileMode z.val) y * Period.meanZeroDirichletPrimitive N (t - y)) := by
    funext y
    by_cases hy : y ∈ Ioc (0 : ℝ) 1 <;> simp [closedQuantileDerivative, hy]
  calc
    _ = ∫ y, closedQuantileDerivative z.val y * Period.meanZeroDirichletPrimitive N (t - y) := by
      rw [he, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le zero_le_one]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [closedQuantileDerivativeL1_ae z] with y hy
      rw [hy]

/-- The original source sums act on an actual, paid whole-line L¹ derivative. -/
theorem sourcePartialSum_eq_L1_derivative_convolution
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (N : ℕ) (t : ℝ) :
    sourcePartialSum z.val N t = (∫ y in (0 : ℝ)..1, closedQuantileMode z.val y) +
      Period.dirichletPrimitiveConvolution N (closedQuantileDerivativeL1 z) t := by
  rw [sourcePartialSum_eq_derivative_convolution, derivative_convolution_eq_L1]

end RHTower.PaperThetaEndpoint
