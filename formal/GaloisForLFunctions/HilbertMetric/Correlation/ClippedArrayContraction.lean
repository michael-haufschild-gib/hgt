import GaloisForLFunctions.HilbertMetric.Spectral.ClippedTrace
import GaloisForLFunctions.HilbertMetric.Correlation.GramContractionDefect

/-!
# Clipped defects of finite array Grams

The existing array mass and Gram contraction are the first two spectral moments.
Their centered combination survives clipping up to the cutoff square. No row
independence, rank condition, or normalization is required.
-/

open Matrix
open scoped NNReal
namespace HilbertMetric.Correlation
open GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section

/-- The complex array Gram has the same real first and second moments. -/
theorem arrayGram_clipped_moments (rows cols : Finset ℕ) (A : ℕ → ℕ → ℝ) :
    ((arrayGram rows cols A).map Complex.ofReal).IsHermitian ∧
      (trace ((arrayGram rows cols A).map Complex.ofReal)).re = arrayMass rows cols A ∧
      (trace (((arrayGram rows cols A).map Complex.ofReal) *
        ((arrayGram rows cols A).map Complex.ofReal))).re = gramContraction rows rows cols A A := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, arrayGram, mul_comm]
  · rw [← arrayGram_trace]
    simp [trace, diag]
  · rw [← arrayGram_trace_mul]
    simp [trace, diag, Matrix.mul_apply]

/-- A trace-contraction surplus cannot disappear under spectral clipping. -/
theorem arrayGram_clippedDefect_lower (rows cols : Finset ℕ) (A : ℕ → ℕ → ℝ) (τ : ℝ≥0) :
    min (gramContraction rows rows cols A A - 2 * arrayMass rows cols A + cols.card)
      ((τ : ℝ) ^ 2) ≤ defectEnergy τ ((arrayGram rows cols A).map Complex.ofReal) := by
  obtain ⟨hH, htr, hsq⟩ := arrayGram_clipped_moments rows cols A
  have h := defectEnergy_min_bound hH τ
  simpa only [htr, hsq, Fintype.card_coe] using h

#print axioms arrayGram_clippedDefect_lower

end
end HilbertMetric.Correlation
