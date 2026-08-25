import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorShortRange

/-!
# Arithmetic moment expansion of the short differentiated detector energy

The short-range coefficient law expands into exactly three harmonic moments: the square of
`Lambda`, its cross moment with `Lambda * Lambda`, and the square of that self-convolution.  This
isolates the precise scalar asymptotics required by the mollified mean-square calculation.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction

namespace RHTower.Sieve

/-- Harmonic square moment of the von Mangoldt weight on the non-unit range. -/
def vonMangoldtHarmonicSquareSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N, (Λ k) ^ 2 / (k : ℝ)

/-- Harmonic cross moment of `Lambda` with its Dirichlet self-convolution. -/
def vonMangoldtSelfConvCrossHarmonicSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N, Λ k * (Λ * Λ) k / (k : ℝ)

/-- Harmonic square moment of the von Mangoldt self-convolution. -/
def vonMangoldtSelfConvHarmonicSquareSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N, ((Λ * Λ) k) ^ 2 / (k : ℝ)

/-- The short differentiated detector energy is exactly a quadratic form in three arithmetic
harmonic moments. -/
theorem sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_momentQuadratic
    (lam : ℝ) {M N : ℕ} (hNM : N ≤ M) :
    ∑ k ∈ Finset.Icc 2 N,
        ‖levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ 2 =
      (((1 - lam * Real.log M) ^ 2 * vonMangoldtHarmonicSquareSum N -
          2 * (1 - lam * Real.log M) * lam *
            vonMangoldtSelfConvCrossHarmonicSum N) +
          lam ^ 2 * vonMangoldtSelfConvHarmonicSquareSum N) /
        (Real.log M) ^ 2 := by
  rw [sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_vonMangoldt lam hNM]
  congr 1
  rw [vonMangoldtHarmonicSquareSum, vonMangoldtSelfConvCrossHarmonicSum,
    vonMangoldtSelfConvHarmonicSquareSum]
  calc
    ∑ k ∈ Finset.Icc 2 N,
        ((1 - lam * Real.log M) * Λ k - lam * (Λ * Λ) k) ^ 2 / (k : ℝ) =
      ∑ k ∈ Finset.Icc 2 N,
        (((1 - lam * Real.log M) ^ 2 * ((Λ k) ^ 2 / (k : ℝ)) -
          (2 * (1 - lam * Real.log M) * lam) *
            (Λ k * (Λ * Λ) k / (k : ℝ))) +
          lam ^ 2 * (((Λ * Λ) k) ^ 2 / (k : ℝ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

end RHTower.Sieve
