import GaloisForLFunctions.RHTower.BernsteinAffineRowCrossMoment
import GaloisForLFunctions.HTGeometry.BernsteinRowDiagonalKernel
import GaloisForLFunctions.HTGeometry.CentralBinomialConvolutionAsymptotic

/-!
# Diagonal affine Bernstein-row asymptotics

One complex affine Bernstein row has an exact central-binomial diagonal kernel.  Its normalized
energy therefore has the universal half-order limit at the row's squared affine amplitude.
-/

open Complex Filter Topology
open scoped BigOperators Real
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Squared Euclidean norm of one complex affine Bernstein row. -/
def bernsteinAffineRowEnergy (u : ℂ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ‖bernsteinAffineRowCoefficient u n k‖ ^ 2

theorem bernsteinAffineRowEnergy_eq_bernsteinRowSquare (u : ℂ) (n : ℕ) :
    bernsteinAffineRowEnergy u n =
      bernsteinRowSquare ‖u‖ ‖1 - u‖ n := by
  rw [bernsteinAffineRowEnergy, bernsteinRowSquare]
  apply Finset.sum_congr rfl
  intro k _
  rw [bernsteinAffineRowCoefficient, norm_mul, norm_mul, norm_pow, norm_pow,
    Complex.norm_natCast]
  ring

/-- Exact diagonal kernel for one complex affine Bernstein row. -/
theorem bernsteinAffineRowEnergy_eq_centralBinomialDiagonalKernelCoefficient
    (u : ℂ) (n : ℕ) :
    bernsteinAffineRowEnergy u n =
      centralBinomialDiagonalKernelCoefficient
        (‖u‖ + ‖1 - u‖) (‖u‖ - ‖1 - u‖) n := by
  rw [bernsteinAffineRowEnergy_eq_bernsteinRowSquare]
  exact bernsteinRowSquare_eq_centralBinomialDiagonalKernelCoefficient _ _ _

/-- Sharp half-order asymptotic of one nondegenerate complex affine Bernstein row. -/
theorem tendsto_sqrtNat_mul_bernsteinAffineRowEnergy_div_pow
    {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt n * bernsteinAffineRowEnergy u n /
          ((‖u‖ + ‖1 - u‖) ^ 2) ^ n)
      atTop
      (nhds ((1 / Real.sqrt Real.pi) *
        ((1 - (‖u‖ - ‖1 - u‖) ^ 2 / (‖u‖ + ‖1 - u‖) ^ 2) ^
          (-1 / 2 : ℝ)))) := by
  rw [show (fun n : ℕ =>
      Real.sqrt n * bernsteinAffineRowEnergy u n /
        ((‖u‖ + ‖1 - u‖) ^ 2) ^ n) =
    fun n : ℕ =>
      Real.sqrt n *
        centralBinomialDiagonalKernelCoefficient
          (‖u‖ + ‖1 - u‖) (‖u‖ - ‖1 - u‖) n /
            ((‖u‖ + ‖1 - u‖) ^ 2) ^ n by
      funext n
      rw [bernsteinAffineRowEnergy_eq_centralBinomialDiagonalKernelCoefficient]]
  apply tendsto_sqrtNat_mul_centralBinomialDiagonalKernelCoefficient_div_pow
  · exact add_pos (norm_pos_iff.mpr hu0)
      (norm_pos_iff.mpr (sub_ne_zero.mpr hu1.symm))
  · rw [abs_lt]
    constructor <;> nlinarith [norm_pos_iff.mpr hu0,
      norm_pos_iff.mpr (sub_ne_zero.mpr hu1.symm)]

end

end RHTower
