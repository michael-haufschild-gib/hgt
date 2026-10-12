import GaloisForLFunctions.RHTower.PaperThetaClosedConvolution
import GaloisForLFunctions.RHTower.PaperThetaQuantileDerivative

/-! # Exact derivative transport of the native Fourier sums

Integration by parts transfers the mean-zero Dirichlet kernel onto the actual
integrable quantile derivative. The common trace and periodic primitive cancel
the boundary term. The global primitive bound then controls every cutoff.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

private theorem hasDerivAt_shifted_primitive (N : ℕ) (t y : ℝ) :
    HasDerivAt (fun x => Period.meanZeroDirichletPrimitive N (t - x))
      (1 - Period.dirichlet N (t - y)) y := by
  convert! (Period.hasDerivAt_meanZeroDirichletPrimitive N (t - y)).scomp y
    ((hasDerivAt_id y).const_sub t) using 1
  simp

/-- The original full Fourier sum is mean plus the actual derivative paired with a bounded kernel. -/
theorem sourcePartialSum_eq_derivative_convolution
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (N : ℕ) (t : ℝ) :
    sourcePartialSum z.val N t = (∫ y in (0 : ℝ)..1, closedQuantileMode z.val y) +
      ∫ y in (0 : ℝ)..1,
        deriv (closedQuantileMode z.val) y * Period.meanZeroDirichletPrimitive N (t - y) := by
  have hf : ContinuousOn (closedQuantileMode z.val) (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using continuousOn_closedQuantileMode z
  have hv : Continuous (fun y => Period.meanZeroDirichletPrimitive N (t - y)) :=
    (Period.continuous_meanZeroDirichletPrimitive N).comp (continuous_const.sub continuous_id)
  have hD : Continuous (fun y => Period.dirichlet N (t - y)) :=
    (Period.dirichlet_cont N).comp (continuous_const.sub continuous_id)
  have hd (y : ℝ) (hy : y ∈ Ioo (min (0 : ℝ) 1) (max 0 1)) :
      HasDerivAt (closedQuantileMode z.val) (deriv (closedQuantileMode z.val) y) y := by
    apply (differentiableAt_closedQuantileMode z.val ⟨y, ?_⟩).hasDerivAt
    simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hy
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hf hv.continuousOn
    hd (fun y _ => hasDerivAt_shifted_primitive N t y)
    (intervalIntegrable_deriv_closedQuantileMode z)
    ((continuous_const.sub hD).intervalIntegrable 0 1)
  rw [(closedQuantileMode_endpoints z.val).1, (closedQuantileMode_endpoints z.val).2,
    (Period.meanZeroDirichletPrimitive_periodic N).sub_eq t, sub_zero, sub_self, zero_sub] at hp
  simp_rw [mul_sub, mul_one] at hp
  rw [intervalIntegral.integral_sub hf.intervalIntegrable
    (hf.intervalIntegrable.mul_continuousOn hD.continuousOn),
    ← sourcePartialSum_eq_closed_convolution z N t] at hp
  linear_combination -hp

/-- A frequency-independent bound paid by the native derivative's total mass. -/
theorem norm_sourcePartialSum_sub_mean_le
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (N : ℕ) (t : ℝ) :
    ‖sourcePartialSum z.val N t - (∫ y in (0 : ℝ)..1, closedQuantileMode z.val y)‖ ≤
      (5 / 2) * ∫ y in (0 : ℝ)..1, ‖deriv (closedQuantileMode z.val) y‖ := by
  rw [sourcePartialSum_eq_derivative_convolution, add_sub_cancel_left]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1) zero_le_one
    (f := fun y => deriv (closedQuantileMode z.val) y * Period.meanZeroDirichletPrimitive N (t - y))
    (g := fun y => ‖deriv (closedQuantileMode z.val) y‖ * (5 / 2))
    (Eventually.of_forall fun y _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (Period.norm_meanZeroDirichletPrimitive_le N (t - y))
        (norm_nonneg _))
    ((intervalIntegrable_deriv_closedQuantileMode z).norm.mul_const (5 / 2))
  rw [intervalIntegral.integral_mul_const] at hb
  simpa only [mul_comm] using hb

end RHTower.PaperThetaEndpoint
