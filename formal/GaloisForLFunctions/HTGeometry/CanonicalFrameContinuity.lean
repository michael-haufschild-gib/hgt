import GaloisForLFunctions.HTGeometry.CanonicalFrameClosedGraph
import GaloisForLFunctions.HTGeometry.CholeskyDeterminantDivergence
import Mathlib.Analysis.Matrix.Normed

/-!
# Continuity of the canonical inverse-Cholesky factor

The closed graph from `CanonicalFrameClosedGraph` is promoted here to genuine continuity.  The
quantitative compactness input is the coordinate estimate
`|C i j|² ≤ (G⁻¹ j j).re`, obtained from `G⁻¹ = Cᴴ C`.  It bounds every canonical frame in
a compact matrix ball whenever the inverse Gram matrices remain locally bounded.  Uniqueness of
the canonical frame then makes every cluster point equal to the frame at the limiting Gram
matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Filter Topology
open scoped Matrix.Norms.Elementwise Topology BigOperators ComplexOrder

noncomputable section

variable {N : ℕ}

/-- Matrix inversion is continuous at every nonsingular finite complex matrix. -/
theorem continuousAt_matrix_inv_of_det_ne_zero
    {G : Matrix (Fin N) (Fin N) ℂ} (hdet : G.det ≠ 0) :
    ContinuousAt (fun H : Matrix (Fin N) (Fin N) ℂ => H⁻¹) G := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  fun_prop

/-- Every squared frame entry is bounded by the corresponding diagonal entry of the inverse
Gram matrix. -/
theorem frame_entry_sq_le_inv_diag
    (C G : Matrix (Fin N) (Fin N) ℂ) (hC : IsInverseCholeskyFrame C G)
    (i j : Fin N) :
    ‖C i j‖ ^ (2 : ℕ) ≤ (G⁻¹ j j).re := by
  have hinv := inverse_eq_conjTranspose_mul_of_inverseCholesky C G hC
  have hentry := congrArg Complex.re (congrFun (congrFun hinv j) j)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hentry
  rw [hentry]
  change ‖C i j‖ ^ (2 : ℕ) ≤ Complex.reCLM (∑ x, star (C x j) * C x j)
  rw [map_sum]
  change ‖C i j‖ ^ (2 : ℕ) ≤ ∑ x, (star (C x j) * C x j).re
  simp only [RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add]
  rw [Complex.sq_norm, Complex.normSq_apply]
  exact Finset.single_le_sum
    (f := fun x : Fin N => (C x j).re * (C x j).re + (C x j).im * (C x j).im)
    (fun k hk => by
      nlinarith [sq_nonneg (C k j).re, sq_nonneg (C k j).im])
    (Finset.mem_univ i)

/-- The elementwise matrix norm of an inverse-Cholesky frame is controlled by the inverse Gram
norm.  The harmless additive `1` avoids taking square roots in the compactness argument. -/
theorem frame_norm_le_inv_norm_add_one
    (C G : Matrix (Fin N) (Fin N) ℂ) (hC : IsInverseCholeskyFrame C G) :
    ‖C‖ ≤ ‖G⁻¹‖ + 1 := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  calc
    ‖C i j‖ ≤ ‖C i j‖ ^ (2 : ℕ) + 1 := by nlinarith [norm_nonneg (C i j)]
    _ ≤ (G⁻¹ j j).re + 1 := by
      nlinarith [frame_entry_sq_le_inv_diag C G hC i j]
    _ ≤ ‖G⁻¹ j j‖ + 1 := by nlinarith [Complex.re_le_norm (G⁻¹ j j)]
    _ ≤ ‖G⁻¹‖ + 1 := by
      nlinarith [Matrix.norm_entry_le_entrywise_sup_norm (G⁻¹) (i := j) (j := j)]

/-- The canonical positive-diagonal inverse-Cholesky factor as a function on the
positive-definite cone. -/
noncomputable def canonicalInverseCholeskyFactor (G : PositiveDefiniteGram N) :
    Matrix (Fin N) (Fin N) ℂ :=
  gramSchmidtInverseFrame G.1 G.2

theorem canonicalInverseCholeskyFactor_isCanonical (G : PositiveDefiniteGram N) :
    IsCanonicalInverseCholeskyFrame (canonicalInverseCholeskyFactor G) G.1 :=
  gramSchmidtInverseFrame_isCanonical G.1 G.2

/-- The canonical inverse-Cholesky factor is continuous at every positive-definite Gram
matrix. -/
theorem continuousAt_canonicalInverseCholeskyFactor (G : PositiveDefiniteGram N) :
    ContinuousAt canonicalInverseCholeskyFactor G := by
  have hdet : G.1.det ≠ 0 := ne_of_gt G.2.det_pos
  have hinvcont : ContinuousAt (fun H : PositiveDefiniteGram N => H.1⁻¹) G :=
    (continuousAt_matrix_inv_of_det_ne_zero hdet).comp continuousAt_subtype_val
  have hnormcont : Tendsto (fun H : PositiveDefiniteGram N => ‖H.1⁻¹‖) (𝓝 G)
      (𝓝 ‖G.1⁻¹‖) := hinvcont.norm
  let R : ℝ := ‖G.1⁻¹‖ + 2
  have heventInv : ∀ᶠ H : PositiveDefiniteGram N in 𝓝 G, ‖H.1⁻¹‖ < ‖G.1⁻¹‖ + 1 :=
    (tendsto_order.1 hnormcont).2 _ (by linarith)
  have heventFrame : ∀ᶠ H : PositiveDefiniteGram N in 𝓝 G,
      canonicalInverseCholeskyFactor H ∈ Metric.closedBall 0 R := by
    filter_upwards [heventInv] with H hH
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (frame_norm_le_inv_norm_add_one _ _
      (canonicalInverseCholeskyFactor_isCanonical H).1).trans (by dsimp [R]; linarith)
  have hcompact : IsCompact (Metric.closedBall (0 : Matrix (Fin N) (Fin N) ℂ) R) :=
    ProperSpace.isCompact_closedBall 0 R
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt heventFrame
  intro C hCball hcluster
  have hpaircluster : MapClusterPt (G, C) (𝓝 G)
      (fun H : PositiveDefiniteGram N => (H, canonicalInverseCholeskyFactor H)) := by
    rw [mapClusterPt_iff_frequently]
    intro s hs
    rcases mem_nhds_prod_iff.mp hs with ⟨u, hu, v, hv, huv⟩
    have hfreqC : ∃ᶠ H : PositiveDefiniteGram N in 𝓝 G,
        canonicalInverseCholeskyFactor H ∈ v := hcluster.frequently hv
    exact (hfreqC.and_eventually hu).mono fun H hH => huv ⟨hH.2, hH.1⟩
  have hgraph : (G, C) ∈ canonicalInverseCholeskyGraph N :=
    (isClosed_canonicalInverseCholeskyGraph N).mem_of_mapClusterPt hpaircluster
      (Filter.Eventually.of_forall fun H => canonicalInverseCholeskyFactor_isCanonical H)
  exact canonicalInverseCholeskyFrame_unique G.1 C (canonicalInverseCholeskyFactor G)
    hgraph (canonicalInverseCholeskyFactor_isCanonical G)

/-- **Canonical-frame continuity.** The normalized inverse-Cholesky factor varies continuously on
the full positive-definite cone. -/
theorem continuous_canonicalInverseCholeskyFactor :
    Continuous (canonicalInverseCholeskyFactor : PositiveDefiniteGram N →
      Matrix (Fin N) (Fin N) ℂ) :=
  continuous_iff_continuousAt.mpr continuousAt_canonicalInverseCholeskyFactor

end

end GaloisForLFunctions.HTGeometry
