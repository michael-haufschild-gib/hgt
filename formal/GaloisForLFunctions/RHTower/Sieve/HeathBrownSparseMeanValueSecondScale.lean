import GaloisForLFunctions.RHTower.Sieve.HeathBrownSecondScaleParameters
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueRealIteration

/-!
# Canonically selected Heath--Brown second scale

This module substitutes the literal natural ceiling of
`max(T^(1/3), (R*T)^(1/4))` into the coefficient-faithful real-ratio iteration.  Auxiliary-scale
existence, integrality, and positivity are discharged.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- Exact two-step bound at Heath--Brown's canonical second-branch scale. -/
theorem integral_Icc_normSq_heathBrown_factors_le_selectedSecondScale
    (A B : Finset PNat) (eps : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    {N : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    let N0 : ℕ := heathBrownSecondScale (T : ℝ) (A.card : ℝ)
    let a0 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (19 * (T : ℝ)⁻¹ * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ (2 : ℕ))
    let b0 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      ((2 * (N : ℝ) / (N0 : ℝ)) * (5 / (2 * (T : ℝ))))
    let k : ℝ :=
      ((5 * Real.pi * Real.exp 1 * (T : ℝ) +
          (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
        (heathBrownSquareDivisorScale N0 eta ^ (2 : ℕ) * (25 * Real.pi / 8) *
          (25 * Real.pi / 8))
    let a1 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (15 * (T : ℝ)⁻¹ * ((N0 * N0 : ℕ) : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        ((2 * ((N0 * N0) / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ (2 : ℕ))
    let b1 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (((((N0 * N0) / N0 + 1 : ℕ) : ℝ)) * (5 / (2 * (T : ℝ))))
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ (2 : ℕ)) ≤
      a0 + b0 * Real.sqrt (k * (2 * a1 + b1 ^ (2 : ℕ) * k)) := by
  dsimp only
  apply integral_Icc_normSq_heathBrown_factors_le_twoStepRealRatio
    A B eps q T hT hA hB
  · exact one_le_heathBrownSecondScale (show (1 : ℝ) ≤ (T : ℝ) by linarith)
  · exact heta

end

end RHTower.Sieve
