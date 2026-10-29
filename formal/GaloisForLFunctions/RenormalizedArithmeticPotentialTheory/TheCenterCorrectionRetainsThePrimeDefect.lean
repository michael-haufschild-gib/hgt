import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCollarIsPaidByTheTopAtoms
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCorrectionIsBoundedOnThePole
import GaloisForLFunctions.HTGeometry.SymmetricFormGroundProjection
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheArchimedeanCrossEnergyIsOneSided

/-!
# The center correction costs a tunable fraction of the prime defect

On the harmonic hyperplane the two-pole form vanishes, leaving the negative
center collar. Its exact row potential is paid by the prime defect with a
free Young parameter. The bounded action on the normalized pole transfers
this lower bound to the whole Euclidean horizon.
-/

noncomputable section

open Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticLorentzianGeometry
  SelectiveMultiscaleArithmeticPositivity HTGeometry

/-- The two-pole form factors through the two literal pole coordinates. -/
theorem arithmeticPoleKernel_quadratic_eq (N : ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, a n * a j * arithmeticPoleKernel n j) =
      2 * SelectiveMultiscaleArithmeticPositivity.harmonicSum N a * (∑ n ∈ Icc 1 N, a n * Real.sqrt n) := by
  have hterm (n j : ℕ) : a n * a j * arithmeticPoleKernel n j =
      (a n * Real.sqrt n) * (a j / Real.sqrt j) +
        (a n / Real.sqrt n) * (a j * Real.sqrt j) := by
    unfold arithmeticPoleKernel
    ring
  simp only [hterm, sum_add_distrib, ← mul_sum, ← sum_mul, SelectiveMultiscaleArithmeticPositivity.harmonicSum]
  ring

/-- On the harmonic hyperplane the center form is the negative collar form. -/
theorem fullWeilCenterMatrix_inner_of_harmonicSum_zero (α : ℝ) {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hx : SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) = 0) :
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) x, x⟫ =
      -α * ((∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension x n * primeHorizonExtension x j * archimedeanCenterKernel n j) / N) := by
  change ⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (fun n j => (α / N) *
      (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N) x, x⟫ = _
  rw [horizonKernelMatrix_inner]
  have hterm (n j : ℕ) :
      primeHorizonExtension x n * primeHorizonExtension x j *
          ((α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) =
        (α / N) * (primeHorizonExtension x n * primeHorizonExtension x j *
          arithmeticPoleKernel n j) -
        (α / N) * (primeHorizonExtension x n * primeHorizonExtension x j *
          archimedeanCenterKernel n j) := by ring
  simp only [hterm, sum_sub_distrib, ← mul_sum]
  rw [arithmeticPoleKernel_quadratic_eq, hx]
  ring

/-- A tunable lower bound for the center form on the harmonic hyperplane. -/
theorem fullWeilCenterMatrix_inner_ge_on_harmonic_hyperplane
    {α lam : ℝ} (hα : 0 ≤ α) (hlam : 0 < lam) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hx : SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) = 0) :
    -α * (1 + 1 / lam) * poleDefect N (primeHorizonExtension x) -
        α * ((1 + lam) * psiConstant + 3) * ‖x‖ ^ 2 ≤
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) x, x⟫ := by
  have hcollar := collar_quadratic_div_horizon_le hN (primeHorizonExtension x)
  have htop := sum_top_le_poleDefect_param N (primeHorizonExtension x) hlam
  rw [sum_primeHorizonExtension_sq] at hcollar htop
  have hupper := hcollar.trans (add_le_add htop (le_refl (3 * ‖x‖ ^ 2)))
  have h := mul_le_mul_of_nonneg_left hupper hα
  rw [fullWeilCenterMatrix_inner_of_harmonicSum_zero α x hx]
  linarith only [h]

/-- The complete center correction costs at most a tunable defect fraction plus mass. -/
theorem fullWeilCenterMatrix_inner_ge
    {α lam : ℝ} (hα : 0 ≤ α) (hlam : 0 < lam) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    -α * (1 + 1 / lam) * poleDefect N (primeHorizonExtension x) -
        α * ((1 + lam) * psiConstant + 15) * ‖x‖ ^ 2 ≤
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) x, x⟫ := by
  have hprojected := fullWeilCenterMatrix_inner_ge_on_harmonic_hyperplane hα hlam hN
    (horizonPoleProjection x) (harmonicSum_horizonPoleProjection hN x)
  rw [poleDefect_horizonPoleProjection hN] at hprojected
  have hcoef : 0 ≤ α * ((1 + lam) * psiConstant + 3) := by
    exact mul_nonneg hα (add_nonneg
      (mul_nonneg (by linarith only [hlam]) psiConstant_pos.le) (by norm_num))
  have hcontract := mul_le_mul_of_nonneg_left
    (horizonPoleProjection_norm_sq_le hN x) hcoef
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (fullWeilCenterMatrix_isHermitian α N)
  have hchange := abs_symmetricForm_sub_groundProjection_le
    (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)) hsym
    (normalizedHorizonPoleVector_norm hN)
    (norm_fullWeilCenterMatrix_normalizedPole_le hα hN) x
  change |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) x, x⟫ -
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (horizonPoleProjection x),
      horizonPoleProjection x⟫| ≤ 3 * (4 * α) * ‖x‖ ^ 2 at hchange
  have hlower := (abs_le.mp hchange).1
  linarith only [hprojected, hcontract, hlower]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
