import GaloisForLFunctions.HilbertMetric.Spectral.ClippedPinching
import GaloisForLFunctions.HilbertMetric.DegreeFiveGaussianCurvature

/-!
# Gaussian overlap survives mixed column multiplicities

Every finite Gaussian distance matrix has unit diagonal and is Hermitian,
including repeated points. Its centered square energy is exactly total squared
overlap minus the number of points. The clipped defect retains that overlap up
to the cutoff square, and survives any independent doubling of columns.

These statements even hold at negative bandwidth: the mixed inequality uses
Hermitian symmetry and unit diagonal, without positive semidefiniteness.
-/

open Matrix
open scoped NNReal
namespace GaloisForLFunctions.HilbertMetric
open Clipped
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype ι] [DecidableEq ι] in
theorem gaussianDistance_complex_hermitian (x : ι → κ → ℝ) (t : ℝ) :
    ((finiteGaussianDistanceGram x t).map (Complex.ofReal)).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
    Complex.conj_ofReal]
  congr 1
  unfold finiteGaussianDistanceGram
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem gaussianDistance_clipped_overlap (x : ι → κ → ℝ) (t : ℝ) (τ : ℝ≥0) :
    min ((∑ i, ∑ j, (finiteGaussianDistanceGram x t i j) ^ 2) - Fintype.card ι)
      ((τ : ℝ) ^ 2) ≤ defectEnergy τ ((finiteGaussianDistanceGram x t).map Complex.ofReal) := by
  have h := defectEnergy_min_bound (gaussianDistance_complex_hermitian x t) τ
  rw [trace_square (gaussianDistance_complex_hermitian x t)] at h
  have ht : (trace ((finiteGaussianDistanceGram x t).map Complex.ofReal)).re =
      Fintype.card ι := by
    simp [trace, diag, finiteGaussianDistanceGram]
  rw [ht] at h
  simp only [Matrix.map_apply, Complex.normSq_ofReal, ← pow_two] at h
  convert h using 1
  congr 1
  ring

/-- Gaussian overlap remains visible when any subset of points receives double weight. -/
theorem gaussianDistance_mixed_clipping (x : ι → κ → ℝ) (t : ℝ)
    (doubled : ι → Bool) (τ : ℝ≥0) :
    defectEnergy τ ((finiteGaussianDistanceGram x t).map Complex.ofReal) +
      ∑ i, binaryWeight doubled i ^ 2 ≤
        energy (mixedCutoff τ) (weightedGram (binaryWeight doubled)
          ((finiteGaussianDistanceGram x t).map Complex.ofReal)) := by
  apply binary_mixed_bound (gaussianDistance_complex_hermitian x t)
  intro i
  simp [finiteGaussianDistanceGram]

/-- An explicit lower bound uses only squared Gaussian overlaps and selected multiplicities. -/
theorem gaussianDistance_mixed_overlap_lower (x : ι → κ → ℝ) (t : ℝ)
    (doubled : ι → Bool) (τ : ℝ≥0) :
    min ((∑ i, ∑ j, (finiteGaussianDistanceGram x t i j) ^ 2) - Fintype.card ι)
        ((τ : ℝ) ^ 2) + ∑ i, binaryWeight doubled i ^ 2 ≤
      energy (mixedCutoff τ) (weightedGram (binaryWeight doubled)
        ((finiteGaussianDistanceGram x t).map Complex.ofReal)) :=
  (add_le_add (gaussianDistance_clipped_overlap x t τ) le_rfl).trans
    (gaussianDistance_mixed_clipping x t doubled τ)

/-- The coherent half-bandwidth convention inherits the identical overlap bound. -/
theorem halfGaussianDistance_mixed_clipping (x : ι → κ → ℝ) (t : ℝ)
    (doubled : ι → Bool) (τ : ℝ≥0) :
    defectEnergy τ ((finiteHalfGaussianDistanceGram x t).map Complex.ofReal) +
      ∑ i, binaryWeight doubled i ^ 2 ≤
        energy (mixedCutoff τ) (weightedGram (binaryWeight doubled)
          ((finiteHalfGaussianDistanceGram x t).map Complex.ofReal)) :=
  gaussianDistance_mixed_clipping x (t / 2) doubled τ

#print axioms gaussianDistance_mixed_overlap_lower
#print axioms halfGaussianDistance_mixed_clipping

end

section Clusters
variable {β κ : Type*} [Fintype β] [DecidableEq β] [Fintype κ]
  {ι : β → Type*} [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]

/-- Disjoint Gaussian clusters contribute separate overlap gains, even when mutually coupled. -/
theorem gaussianDistance_clustered_mixed_lower (x : (Σ b, ι b) → κ → ℝ) (t : ℝ)
    (doubled : (Σ b, ι b) → Bool) (τ : ℝ≥0) :
    (∑ b, min ((∑ i : ι b, ∑ j : ι b,
        (finiteGaussianDistanceGram (fun k => x ⟨b, k⟩) t i j) ^ 2) - Fintype.card (ι b))
      ((τ : ℝ) ^ 2)) + ∑ i, binaryWeight doubled i ^ 2 ≤
      energy (mixedCutoff τ) (weightedGram (binaryWeight doubled)
        ((finiteGaussianDistanceGram x t).map Complex.ofReal)) := by
  have hm := mixed_block_defects (gaussianDistance_complex_hermitian x t)
    (fun i => by simp [finiteGaussianDistanceGram]) doubled τ
  exact (add_le_add (Finset.sum_le_sum fun b _ =>
    gaussianDistance_clipped_overlap (fun k => x ⟨b, k⟩) t τ) le_rfl).trans hm

#print axioms gaussianDistance_clustered_mixed_lower

end Clusters
end GaloisForLFunctions.HilbertMetric
