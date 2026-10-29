import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixHasAnExactErrorDecomposition
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCorrectionHasBoundedPoleResidual
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleProjectionIsTheEuclideanGroundProjection

/-!
# The complete center correction is bounded on the normalized pole

Exact cancellation leaves a square-bounded residual on the unnormalized pole.
Its harmonic mass is at least one, so the complete center matrix has norm at
most four times its nonnegative charge on the normalized ground direction.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SelectiveMultiscaleArithmeticPositivity

/-- The actual center matrix has the exact finite harmonic boundary residual bound. -/
theorem fullWeilCenterMatrix_pole_residual_sq_le (α : ℝ) (N : ℕ) :
    ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (horizonPoleVector N) -
      α • horizonPoleVector N‖ ^ 2 ≤ 6 * α ^ 2 := by
  change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => (α / N) *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j)) N)
      (horizonProfileVector (fun n => 1 / Real.sqrt n) N) -
      α • horizonProfileVector (fun n => 1 / Real.sqrt n) N‖ ^ 2 ≤ _
  rw [horizonKernelMatrix_profile_residual_norm_sq]
  simpa only [mul_assoc, mul_one_div, mul_div_assoc, ← mul_sum] using
    sum_sq_centerCorrection_pole_residual_le α N

/-- A nonnegative center charge has uniformly bounded action on the normalized pole. -/
theorem norm_fullWeilCenterMatrix_normalizedPole_le {α : ℝ} (hα : 0 ≤ α)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedHorizonPoleVector N)‖ ≤ 4 * α := by
  have hH := harmonicMass_pos hN
  have hs0 : 0 < Real.sqrt (harmonicMass N) := Real.sqrt_pos.mpr hH
  have hsquare := horizonPoleVector_norm_sq N
  have hnorm : ‖horizonPoleVector N‖ = Real.sqrt (harmonicMass N) := by
    rw [← hsquare, Real.sqrt_sq (norm_nonneg _)]
  have hnorm1 : 1 ≤ ‖horizonPoleVector N‖ := by
    rw [hnorm]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (one_le_harmonicMass hN)
  have hres := fullWeilCenterMatrix_pole_residual_sq_le α N
  have hrnorm :
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (horizonPoleVector N) -
        α • horizonPoleVector N‖ ≤ 3 * α := by
    have hsq :
        ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (horizonPoleVector N) -
          α • horizonPoleVector N‖ ^ 2 ≤ (3 * α) ^ 2 := by
      nlinarith only [hres, sq_nonneg α]
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hα)] at h
    exact h
  have hraw : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (horizonPoleVector N)‖ ≤
      4 * α * ‖horizonPoleVector N‖ := by
    calc
      _ = ‖(Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (horizonPoleVector N) -
          α • horizonPoleVector N) + α • horizonPoleVector N‖ := by rw [sub_add_cancel]
      _ ≤ ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (horizonPoleVector N) -
          α • horizonPoleVector N‖ + ‖α • horizonPoleVector N‖ := norm_add_le _ _
      _ ≤ 3 * α + α * ‖horizonPoleVector N‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
        exact add_le_add hrnorm le_rfl
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hnorm1 hα
        nlinarith only [h]
  rw [hnorm] at hraw
  rw [normalizedHorizonPoleVector, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hs0]
  calc
    _ ≤ (Real.sqrt (harmonicMass N))⁻¹ * (4 * α * Real.sqrt (harmonicMass N)) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hs0.le)
    _ = _ := by field_simp [hs0.ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
