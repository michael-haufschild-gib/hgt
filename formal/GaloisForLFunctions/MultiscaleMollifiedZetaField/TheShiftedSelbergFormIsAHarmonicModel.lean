import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergEulerFactorsCancel
import GaloisForLFunctions.RHTower.Sieve.SelbergWeightedConvolutionModel

/-!
# The shifted Selberg form as a harmonic Möbius model

The exact Euler factorization keeps an arbitrary finite weight inside
its Möbius transforms. The gcd shift changes only the diagonal harmonic
weight and the absolutely summable correction fibres.
-/

open Finset
open RHTower.Sieve
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem shiftedSelbergDiagonal_double_sum (c : ℝ)
    {X Y : ℕ} (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
      shiftedSelbergDiagonal c d e * F d e) =
    ∑ d ∈ Finset.Icc 1 (min X Y), (1 / (d : ℝ)) * ((d : ℝ) ^ c * F d d) := by
  simpa only [shiftedSelbergDiagonal, mul_assoc] using
    selbergDiagonalReciprocalCoeff_double_sum_mul_eq (X := X) (Y := Y)
      (fun d e => (d : ℝ) ^ c * F d e)

/-- The shifted principal convolution is a single power-weighted harmonic sum. -/
theorem shiftedSelbergPrincipal_weighted_eq_harmonic_model
    (c : ℝ) (w : ℕ → ℝ) (N a b : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
      shiftedSelbergPrincipal c r s * (w (a * r) * w (b * s))) =
    ∑ d ∈ Finset.Icc 1 (min (N / a) (N / b)),
      (d : ℝ) ^ c * (selbergMoebiusWeightedSum w N (a * d) *
        selbergMoebiusWeightedSum w N (b * d)) / d := by
  simp only [shiftedSelbergPrincipal]
  rw [sum_Icc_bivariateDirichletConvolution_mul, shiftedSelbergDiagonal_double_sum]
  apply Finset.sum_congr rfl
  intro d _
  have hinner :
      (∑ r ∈ Finset.Icc 1 (N / a / d), ∑ s ∈ Finset.Icc 1 (N / b / d),
        selbergMoebiusReciprocalPair r s * (w (a * (d * r)) * w (b * (d * s)))) =
      selbergMoebiusWeightedSum w N (a * d) * selbergMoebiusWeightedSum w N (b * d) := by
    simp only [selbergMoebiusWeightedSum, Nat.div_div_eq_div_mul]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    simp only [selbergMoebiusReciprocalPair, Nat.mul_assoc]
    ring
  rw [hinner]
  ring

/-- Exact finite correction identity for every real gcd shift and finite weight. -/
theorem shiftedSelbergOriginal_weighted_eq_correction_harmonic_model
    (c : ℝ) (w : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      shiftedSelbergOriginal c m n * (w m * w n)) =
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      shiftedSelbergCorrectionCoeff c a b *
        (∑ d ∈ Finset.Icc 1 (min (N / a) (N / b)),
          (d : ℝ) ^ c * (selbergMoebiusWeightedSum w N (a * d) *
            selbergMoebiusWeightedSum w N (b * d)) / d) := by
  simp only [← shiftedSelbergCorrection_convolution_principal]
  rw [sum_Icc_bivariateDirichletConvolution_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [shiftedSelbergPrincipal_weighted_eq_harmonic_model]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
