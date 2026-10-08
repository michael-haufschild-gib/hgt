import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialMellinBound

/-!
# Quadratic constraints on the actual normalized parity series

The alternating series is evaluated in its absolute-convergence half-plane.
No limiting value, meromorphic continuation, or Laurent coefficient is assumed.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

def sourceNormalizedParityPole (lam : ℕ → ℝ) (σ : ℝ) : ℝ :=
  (σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) * sourceAlternatingZetaSquare lam (σ : ℂ)).re

theorem exists_source_normalized_parity_quadratic_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) :
    ∃ B : ℝ, ∀ σ : ℝ, 1 < σ → σ < 3 / 2 →
      (1 + c ^ 2 / 2 - c * (4 : ℝ) ^ (-(σ / 2))) *
          ((σ - 1) ^ 2 * (mellin (sourceGaussianProfile lam) ((σ : ℂ) / 2)).re) -
        (c / 2) * (1 / 4 : ℝ) ^ (-(σ / 2)) * sourceNormalizedParityPole lam σ ≤
      (σ - 1) ^ 2 * B := by
  obtain ⟨B, hB⟩ := exists_re_mellin_sourceTwoPointGaussianProfile_le hW c
  refine ⟨B, fun σ hσ hσ' => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hB σ hσ hσ') (sq_nonneg (σ - 1))
  rw [re_mellin_sourceTwoPointGaussianProfile_eq hW c hσ] at h
  dsimp only [sourceNormalizedParityPole]
  nlinarith only [h]

end RHTower.WeilSingularArithmetic
