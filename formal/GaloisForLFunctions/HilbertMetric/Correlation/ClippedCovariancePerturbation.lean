import GaloisForLFunctions.HilbertMetric.Spectral.ClippedThreshold
import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyFiniteWindowInertia
import GaloisForLFunctions.HilbertMetric.CrouzeixEvaluationEnergy

/-!
# Clipped energy under covariance subtraction and signed additions

Subtracting an arbitrary covariance pays only its trace cost. For a signed
covariance addition, the threshold penalty is bounded by the rank of the added
positive covariance; the subtracted covariance may have arbitrary rank.
Prescribed evaluation packets inherit both source-target invariance and the
subtraction inequality without requiring reconstructibility.
-/

open Matrix
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric
open Clipped
noncomputable section
variable {h x y z : Type*} [Fintype h] [DecidableEq h]
  [Fintype x] [Fintype y] [Fintype z]

/-- Removing a covariance pays at most a linear trace charge against clipped energy. -/
theorem covariance_subtraction_clipped (A : Matrix h x ℂ) (B : Matrix h y ℂ) (c : ℝ) :
    energy c (A * Aᴴ) ≤
      (trace ((A * Aᴴ - B * Bᴴ) * (A * Aᴴ - B * Bᴴ))).re +
        2 * c * (trace (B * Bᴴ)).re :=
  energy_le_sub_square (Matrix.isHermitian_mul_conjTranspose_self A)
    (Matrix.posSemidef_self_mul_conjTranspose B) c

/-- Only the rank of the added covariance enters the signed perturbation penalty. -/
theorem signed_covariance_clipped_threshold (A : Matrix h x ℂ) (B : Matrix h y ℂ)
    (C : Matrix h z ℂ) (c : ℝ) :
    2 * c * (trace (B * Bᴴ - C * Cᴴ)).re + energy c (A * Aᴴ) -
      c ^ 2 * (B * Bᴴ).rank ≤
        (trace ((A * Aᴴ + (B * Bᴴ - C * Cᴴ)) *
          (A * Aᴴ + (B * Bᴴ - C * Cᴴ)))).re := by
  have hB := Matrix.posSemidef_self_mul_conjTranspose B
  have hC := Matrix.posSemidef_self_mul_conjTranspose C
  have ht := threshold (Matrix.posSemidef_self_mul_conjTranspose A)
    (hB.isHermitian.sub hC.isHermitian) c
  have hi : RiemannGaussian.HermitianRankTrace.posIndex
      (hB.isHermitian.sub hC.isHermitian) ≤ (B * Bᴴ).rank :=
    RiemannGaussian.HermitianInertia.posIndex_sub_le_rank hB hC
  have hir : (RiemannGaussian.HermitianRankTrace.posIndex
      (hB.isHermitian.sub hC.isHermitian) : ℝ) ≤ (B * Bᴴ).rank := by exact_mod_cast hi
  have hp := mul_le_mul_of_nonneg_left hir (sq_nonneg c)
  linarith only [ht, hp]

section Evaluation
variable {κ X Y : Type*} [Fintype κ] [DecidableEq κ]

/-- Feature and sample kernels have identical clipped energy on a prescribed packet. -/
theorem evaluation_clippedEnergy_duality (u : κ → X → ℂ) (p : κ → X) (c : ℝ≥0) :
    energy c (complexEvaluationGram u p) =
      energy c (complexEvaluationMatrix u p * (complexEvaluationMatrix u p)ᴴ) := by
  rw [complexEvaluationGram_eq_conjTranspose_mul]
  exact (energy_gram (complexEvaluationMatrix u p) c).symm

/-- Subtracting a second sampled feature system has an explicit trace cost. -/
theorem evaluation_covariance_clipped (u : κ → X → ℂ) (p : κ → X)
    (v : κ → Y → ℂ) (q : κ → Y) (c : ℝ) :
    energy c (complexEvaluationGram u p) ≤
      (trace ((complexEvaluationGram u p - complexEvaluationGram v q) *
        (complexEvaluationGram u p - complexEvaluationGram v q))).re +
      2 * c * (trace (complexEvaluationGram v q)).re := by
  rw [complexEvaluationGram_eq_conjTranspose_mul, complexEvaluationGram_eq_conjTranspose_mul]
  exact energy_le_sub_square (Matrix.isHermitian_conjTranspose_mul_self _)
    (Matrix.posSemidef_conjTranspose_mul_self _) c

end Evaluation

#print axioms signed_covariance_clipped_threshold
#print axioms evaluation_clippedEnergy_duality
#print axioms evaluation_covariance_clipped

end
end GaloisForLFunctions.HilbertMetric
