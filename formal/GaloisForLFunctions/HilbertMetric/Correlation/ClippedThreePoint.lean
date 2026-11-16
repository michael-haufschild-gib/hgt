import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCongruence
import GaloisForLFunctions.HilbertMetric.ThreePointCorrelation

/-!
# Clipped energy outside the three-point positivity wall

The three-point matrix remains Hermitian for arbitrary real correlations.
Its clipped defect retains the explicit diagonal and edge square energy,
including outside the cubic positive-semidefinite chamber.
-/

open Matrix
open scoped NNReal
namespace HilbertMetric.Correlation
open GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section

theorem threePoint_complex_hermitian (d p q r : ℝ) :
    ((threePointCorrelationMatrix d p q r).map Complex.ofReal).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, threePointCorrelationMatrix]

/-- The three diagonal deviations and six oriented edges give the exact square defect. -/
theorem threePoint_clippedDefect (d p q r : ℝ) (τ : ℝ≥0) :
    min (3 * (d - 1) ^ 2 + 2 * (p ^ 2 + q ^ 2 + r ^ 2)) ((τ : ℝ) ^ 2) ≤
      defectEnergy τ ((threePointCorrelationMatrix d p q r).map Complex.ofReal) := by
  have h := defectEnergy_min_bound (threePoint_complex_hermitian d p q r) τ
  rw [trace_square (threePoint_complex_hermitian d p q r)] at h
  simp [trace, diag, threePointCorrelationMatrix, Fin.sum_univ_three] at h
  convert h using 1
  congr 1
  ring

/-- Every real three-point packet retains its edge surplus after mixed weighting. -/
theorem threePoint_mixed_clipping (p q r : ℝ) (doubled : Fin 3 → Bool) (τ : ℝ≥0) :
    min (2 * (p ^ 2 + q ^ 2 + r ^ 2)) ((τ : ℝ) ^ 2) + ∑ i, binaryWeight doubled i ^ 2 ≤
      energy (mixedCutoff τ) (weightedGram (binaryWeight doubled)
        ((threePointCorrelationMatrix 1 p q r).map Complex.ofReal)) := by
  have h := threePoint_clippedDefect 1 p q r τ
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at h
  have hm := binary_mixed_bound (threePoint_complex_hermitian 1 p q r)
    (fun i => by fin_cases i <;> simp [threePointCorrelationMatrix]) doubled τ
  exact (add_le_add h le_rfl).trans hm

#print axioms threePoint_clippedDefect
#print axioms threePoint_mixed_clipping

end
end HilbertMetric.Correlation
