import GaloisForLFunctions.HilbertMetric.Spectral.ClippedTrace
import GaloisForLFunctions.HilbertMetric.Observation.GramEffectiveDimension

/-!
# Clipped energy detects loss of maximal regularization slope

At unit regularization, the Gram dimension slope is at most one quarter of the
ambient dimension. Its exact rational square defect is bounded by the clipped
quadratic defect, which grows only linearly on the upper spectral tail.
-/

open Matrix
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Observation
open Clipped
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

private theorem relative_square_le_defect {x : ℝ} (hx : 0 ≤ x) :
    (x - 1) ^ 2 / (x + 1) ^ 2 ≤ defect 1 x := by
  by_cases h : x ≤ 2
  · rw [defect_eq_square (by linarith only [h] : x ≤ 1 + 1)]
    apply div_le_self (sq_nonneg _)
    nlinarith only [hx, sq_nonneg x]
  · have hden : 0 < (x + 1) ^ 2 := sq_pos_of_pos (by linarith only [hx])
    have hratio : (x - 1) ^ 2 / (x + 1) ^ 2 ≤ 1 :=
      (div_le_one hden).mpr (by nlinarith only [hx])
    have hcut : 1 + 1 ≤ x := by linarith only [h]
    exact hratio.trans (by simpa using defect_ge_cutoff (by norm_num : (0 : ℝ) ≤ 1) hcut)

/-- The corpus's Gram spectrum computes the clipped matrix defect exactly. -/
theorem gramSpectrum_clippedDefect (A : Matrix m n ℂ) (τ : ℝ) :
    (∑ i, defect τ (gramSpectrum A i)) = defectEnergy τ (Aᴴ * A) :=
  (spectralSum_eq (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian _).symm

/-- Loss of maximal effective-dimension slope forces clipped spectral defect. -/
theorem gramDimensionSlope_clippedDefect (A : Matrix m n ℂ) :
    (Fintype.card n : ℝ) - 4 * gramDimensionSlope A 0 ≤ defectEnergy 1 (Aᴴ * A) := by
  have hid := gramDimensionSlope_sharp_defect A 0
  simp only [Real.exp_zero] at hid
  have hs : (∑ i, (gramSpectrum A i - 1) ^ 2 / (gramSpectrum A i + 1) ^ 2) ≤
      ∑ i, defect 1 (gramSpectrum A i) := by
    apply Finset.sum_le_sum
    intro i _
    exact relative_square_le_defect
      ((Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i)
  have he : (∑ i, (gramSpectrum A i - 1) ^ 2 / (gramSpectrum A i + 1) ^ 2) =
      4 * ∑ i, (gramSpectrum A i - 1) ^ 2 / (4 * (gramSpectrum A i + 1) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_mul_eq_div_div]
    ring
  rw [he, gramSpectrum_clippedDefect] at hs
  linarith only [hs, hid]

/-- The same observation matrix also retains centered square energy up to any cutoff. -/
theorem observation_clippedDefect_lower (A : Matrix m n ℂ) (τ : ℝ≥0) :
    min ((trace ((Aᴴ * A) * (Aᴴ * A))).re - 2 * (trace (Aᴴ * A)).re +
      Fintype.card n) ((τ : ℝ) ^ 2) ≤ defectEnergy τ (Aᴴ * A) :=
  defectEnergy_min_bound (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian τ

#print axioms gramDimensionSlope_clippedDefect
#print axioms observation_clippedDefect_lower

end
end GaloisForLFunctions.HilbertMetric.Observation
