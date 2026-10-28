import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRenormalizedPrimeEnergyControlsTheDefect

/-!
# Exact Euclidean identities on the positive integer horizon

Finite integer kernel rows agree with their Euclidean matrix actions after the
canonical zero extension. The same reindexing gives exact squared norms and
quadratic forms, permitting literal row estimates to control actual matrices.
-/

noncomputable section

open Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- A finite integer profile in Euclidean horizon coordinates. -/
def horizonProfileVector (a : ℕ → ℝ) (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => a n)

/-- Restrict an integer kernel to the actual positive horizon. -/
def horizonKernelMatrix (K : ℕ → ℕ → ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ := fun n j => K n j

theorem horizonProfileVector_norm_sq (a : ℕ → ℝ) (N : ℕ) :
    ‖horizonProfileVector a N‖ ^ 2 = ∑ n ∈ Icc 1 N, a n ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact sum_coe_sort (Icc 1 N) (fun n => a n ^ 2)

/-- Each matrix row is precisely its finite integer-kernel sum. -/
theorem horizonKernelMatrix_apply_profile (K : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (N : ℕ) (n : PrimeHorizonIndex N) :
    (Matrix.toEuclideanLin (horizonKernelMatrix K N) (horizonProfileVector a N)) n =
      ∑ j ∈ Icc 1 N, K n j * a j := by
  change (∑ j : PrimeHorizonIndex N, K n j * a j) = _
  exact sum_coe_sort (Icc 1 N) (fun j => K n j * a j)

/-- Squared matrix residuals are the sums of their literal integer-row squares. -/
theorem horizonKernelMatrix_profile_residual_norm_sq (K : ℕ → ℕ → ℝ)
    (a : ℕ → ℝ) (μ : ℝ) (N : ℕ) :
    ‖Matrix.toEuclideanLin (horizonKernelMatrix K N) (horizonProfileVector a N) -
        μ • horizonProfileVector a N‖ ^ 2 =
      ∑ n ∈ Icc 1 N, ((∑ j ∈ Icc 1 N, K n j * a j) - μ * a n) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq,
    ← sum_coe_sort (Icc 1 N)
      (fun n => ((∑ j ∈ Icc 1 N, K n j * a j) - μ * a n) ^ 2)]
  refine sum_congr rfl fun n _ => ?_
  change ((Matrix.toEuclideanLin (horizonKernelMatrix K N) (horizonProfileVector a N)) n -
    μ * a n) ^ 2 = _
  rw [horizonKernelMatrix_apply_profile]

/-- Matrix action without a spectral shift is the same literal square sum. -/
theorem horizonKernelMatrix_profile_norm_sq (K : ℕ → ℕ → ℝ)
    (a : ℕ → ℝ) (N : ℕ) :
    ‖Matrix.toEuclideanLin (horizonKernelMatrix K N) (horizonProfileVector a N)‖ ^ 2 =
      ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K n j * a j) ^ 2 := by
  simpa only [zero_smul, sub_zero, zero_mul] using
    horizonKernelMatrix_profile_residual_norm_sq K a 0 N

/-- Zero extension is the inverse of restriction on every horizon vector. -/
theorem horizonProfileVector_extension {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    horizonProfileVector (primeHorizonExtension x) N = x := by
  ext n
  exact primeHorizonExtension_coe x n

/-- The Euclidean kernel form is the literal finite double sum. -/
theorem horizonKernelMatrix_inner (K : ℕ → ℕ → ℝ) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (horizonKernelMatrix K N) x, x⟫ =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension x n * primeHorizonExtension x j * K n j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, x n * ∑ j : PrimeHorizonIndex N, K n j * x j) = _
  simp only [mul_sum]
  rw [← sum_coe_sort (Icc 1 N) (fun n => ∑ j ∈ Icc 1 N,
    primeHorizonExtension x n * primeHorizonExtension x j * K n j)]
  refine sum_congr rfl fun n _ => ?_
  rw [← sum_coe_sort (Icc 1 N)
    (fun j => primeHorizonExtension x n * primeHorizonExtension x j * K n j)]
  refine sum_congr rfl fun j _ => ?_
  rw [primeHorizonExtension_coe, primeHorizonExtension_coe]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
