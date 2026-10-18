import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalUpperAsymptotic

/-!
# Exact weighted principal model for the Selberg form

The bivariate Euler correction acts on an arbitrary finite weight through
harmonic products of its Möbius transforms. Keeping the weight inside this
identity permits cancellation between different cutoffs before estimation.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Finite Möbius transform of a weight along the multiples of `q`. -/
def selbergMoebiusWeightedSum (w : ℕ → ℝ) (N q : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 (N / q), selbergMoebiusReciprocalCoeff u * w (q * u)

/-- The principal bivariate convolution collapses to one harmonic sum. -/
theorem selbergPrincipalCoeff_weighted_eq_harmonic_model
    (w : ℕ → ℝ) (N a b : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
      selbergPrincipalCoeff r s * (w (a * r) * w (b * s))) =
    ∑ d ∈ Finset.Icc 1 (min (N / a) (N / b)),
      selbergMoebiusWeightedSum w N (a * d) *
        selbergMoebiusWeightedSum w N (b * d) / d := by
  simp only [selbergPrincipalCoeff]
  rw [sum_Icc_bivariateDirichletConvolution_mul,
    selbergDiagonalReciprocalCoeff_double_sum_mul_eq]
  apply Finset.sum_congr rfl
  intro d _
  have hinner :
      (∑ r ∈ Finset.Icc 1 (N / a / d), ∑ s ∈ Finset.Icc 1 (N / b / d),
        selbergMoebiusReciprocalPair r s * (w (a * (d * r)) * w (b * (d * s)))) =
      selbergMoebiusWeightedSum w N (a * d) *
        selbergMoebiusWeightedSum w N (b * d) := by
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

/-- Exact finite Euler-correction identity for every weight. -/
theorem selbergOriginalCoeff_weighted_eq_correction_harmonic_model
    (w : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      selbergOriginalCoeff m n * (w m * w n)) =
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      selbergEulerCorrectionCoeff a b *
        (∑ d ∈ Finset.Icc 1 (min (N / a) (N / b)),
          selbergMoebiusWeightedSum w N (a * d) *
            selbergMoebiusWeightedSum w N (b * d) / d) := by
  simp only [← selbergEulerCorrection_convolution_principal]
  rw [sum_Icc_bivariateDirichletConvolution_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [selbergPrincipalCoeff_weighted_eq_harmonic_model]

end

end RHTower.Sieve
