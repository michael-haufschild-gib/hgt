import GaloisForLFunctions.HilbertMetric.CentroidGauge

/-!
# Response compression of Hilbert configurations

The common-attraction reduction of Araújo, arXiv:2609.05560, Theorem 2 and equation (8),
acts on the existing centroid and Gaussian distance geometry. These identities hold for every
configuration and every affine scale, without response-cell assumptions: they concern the
linear response operator itself.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric
noncomputable section
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Affine averaging commutes with the centroid of a nonempty finite configuration. -/
theorem hilbertCentroid_response_affine (x : Fin (n + 1) → E) (b : E) (c : ℝ) :
    hilbertCentroid (fun i => b + c • x i) = b + c • hilbertCentroid x := by
  have hn : (Fintype.card (Fin (n + 1)) : ℝ) ≠ 0 := by positivity
  simp only [hilbertCentroid, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, ← Finset.smul_sum,
    smul_add, smul_smul]
  rw [inv_mul_cancel₀ hn, one_smul, mul_comm]

/-- A summary contracts every position about the true centroid. -/
def responseCompression (x : Fin (n + 1) → E) (c : ℝ) : Fin (n + 1) → E :=
  fun i => hilbertCentroid x + c • (x i - hilbertCentroid x)

/-- Compression preserves the statistic governing linear-response translation. -/
theorem hilbertCentroid_responseCompression (x : Fin (n + 1) → E) (c : ℝ) :
    hilbertCentroid (responseCompression x c) = hilbertCentroid x := by
  change hilbertCentroid (fun i => hilbertCentroid x + c • (x i - hilbertCentroid x)) = _
  rw [hilbertCentroid_response_affine]
  have hz : hilbertCentroid (fun i => x i - hilbertCentroid x) = 0 := by
    change (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ •
      (∑ i, (x i - hilbertCentroid x)) = 0
    rw [sum_sub_hilbertCentroid]
    simp
  rw [hz]
  simp

/-- The centered summary is exactly the scaled original disagreement. -/
theorem responseCompression_centered (x : Fin (n + 1) → E) (c : ℝ) (i : Fin (n + 1)) :
    responseCompression x c i - hilbertCentroid (responseCompression x c) =
      c • (x i - hilbertCentroid x) := by
  rw [hilbertCentroid_responseCompression]
  simp [responseCompression]

/-- Every pairwise displacement scales by the same factor. -/
theorem responseCompression_sub (x : Fin (n + 1) → E) (c : ℝ)
    (i j : Fin (n + 1)) :
    responseCompression x c i - responseCompression x c j = c • (x i - x j) := by
  simp only [responseCompression]
  module

/-- The existing centered Hilbert energy retains exactly the square of the compression scale. -/
theorem responseCompression_energy (x : Fin (n + 1) → E) (c : ℝ) :
    (∑ i, ‖responseCompression x c i - hilbertCentroid (responseCompression x c)‖ ^ 2) =
      c ^ 2 * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2 := by
  simp_rw [responseCompression_centered, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact (Finset.mul_sum ..).symm

/-- Compression is equivalent to changing the inverse squared Gaussian bandwidth. -/
theorem gaussianDistanceMatrix_responseCompression (x : Fin (n + 1) → E) (c t : ℝ) :
    gaussianDistanceMatrix (responseCompression x c) t = gaussianDistanceMatrix x (t * c ^ 2) := by
  ext i j
  simp only [gaussianDistanceMatrix, responseCompression_sub, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  congr 1
  ring

/-- The same bandwidth law holds for the Gaussian volume determinant. -/
theorem gaussianDistanceMatrix_det_responseCompression (x : Fin (n + 1) → E) (c t : ℝ) :
    (gaussianDistanceMatrix (responseCompression x c) t).det =
      (gaussianDistanceMatrix x (t * c ^ 2)).det := by
  rw [gaussianDistanceMatrix_responseCompression]

omit [InnerProductSpace ℝ E] in
/-- Shared translation is invisible to the Gaussian distance matrix. -/
theorem gaussianDistanceMatrix_common_translation (x : Fin (n + 1) → E) (b : E) (t : ℝ) :
    gaussianDistanceMatrix (fun i => x i + b) t = gaussianDistanceMatrix x t := by
  ext i j
  simp [gaussianDistanceMatrix]

/-- A shared attractive anchor moves the centroid toward the anchor. -/
theorem hilbertCentroid_common_anchor (x : Fin (n + 1) → E) (b : E) (lam : ℝ) :
    hilbertCentroid (fun i => lam • (b - x i)) = lam • (b - hilbertCentroid x) := by
  have h := hilbertCentroid_response_affine x (lam • b) (-lam)
  simpa [smul_sub, neg_smul, sub_eq_add_neg] using h

/-- Subtracting the mean velocity erases the shared anchor exactly. -/
theorem common_anchor_disagreement (x : Fin (n + 1) → E) (b : E) (lam : ℝ)
    (i : Fin (n + 1)) :
    lam • (b - x i) - hilbertCentroid (fun j => lam • (b - x j)) =
      -lam • (x i - hilbertCentroid x) := by
  rw [hilbertCentroid_common_anchor]
  module

/-- Two summaries with arbitrary different anchors induce identical centered velocities. -/
theorem common_anchor_shape_blind (x : Fin (n + 1) → E) (b d : E) (lam : ℝ) :
    (fun i => lam • (b - x i) - hilbertCentroid (fun j => lam • (b - x j))) =
      (fun i => lam • (d - x i) - hilbertCentroid (fun j => lam • (d - x j))) := by
  funext i
  rw [common_anchor_disagreement, common_anchor_disagreement]

end
end GaloisForLFunctions.HilbertMetric
