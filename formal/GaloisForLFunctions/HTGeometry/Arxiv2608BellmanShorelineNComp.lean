import GaloisForLFunctions.HTGeometry.Arxiv2608BellmanShorelineTwoHalfCells

/-!
# Finite N-COMP estimates from arXiv:2608.29060

This module formalizes dimension-free estimates used when N-COMP removes rectifiable-cell and
compact-domain infinities: conservative polygonal ratio loss, normalized compact-box bounds, and
support stability under one-sided Hausdorff containment. These are independent of companion
paper's bounded-cell theorem and of any numerical search or quantifier-elimination implementation.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

/-- Elementary distortion estimate used by conservative polygonalization. -/
theorem bellmanShoreline_inv_one_sub_le
    {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2) :
    (1 - h)⁻¹ ≤ 1 + 2 * h := by
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  nlinarith

/-- Multiplicative ratio loss under support erosion by at most half normalized margin. -/
theorem bellmanShoreline_polygonalRatio_le
    {R h : ℝ} (hR : 0 ≤ R) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2) :
    R / (1 - h) ≤ R * (1 + 2 * h) := by
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (bellmanShoreline_inv_one_sub_le hh0 hh) hR

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Compact-box anchor estimate in N-COMP normalization. -/
theorem bellmanShoreline_anchor_norm_le_one_third
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ 1 / 4)
    {p0 pn : F} (hp0 : p0 = lambda • pn) (hgap : ‖pn - p0‖ ≤ 1) :
    ‖p0‖ ≤ 1 / 3 := by
  rw [hp0, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlambda0]
  rw [hp0] at hgap
  have hdiff : pn - lambda • pn = (1 - lambda) • pn := by module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hgap
  nlinarith [norm_nonneg pn]

omit [InnerProductSpace ℝ F] in
/-- Every vertex within unit path distance of N-COMP anchor lies in radius `4/3` box. -/
theorem bellmanShoreline_vertex_norm_le_four_thirds
    {p0 p : F} (hp0 : ‖p0‖ ≤ 1 / 3) (hp : ‖p - p0‖ ≤ 1) :
    ‖p‖ ≤ 4 / 3 := by
  calc
    ‖p‖ = ‖(p - p0) + p0‖ := by rw [sub_add_cancel]
    _ ≤ ‖p - p0‖ + ‖p0‖ := norm_add_le _ _
    _ ≤ 4 / 3 := by linarith

/-- Closed metric thickening used to compare original and polygonal historical hulls. -/
def bellmanShorelineThickening (L : Set F) (h : ℝ) : Set F :=
  {x | ∃ y ∈ L, ‖x - y‖ ≤ h}

/-- Hausdorff one-sided containment lowers support by at most `h‖n‖`. -/
theorem bellmanShorelineSupport_le_of_subset_thickening
    {K L : Set F} {h : ℝ} (hKne : K.Nonempty)
    (hLcompact : IsCompact L)
    (hsub : K ⊆ bellmanShorelineThickening L h) (n : F) :
    bellmanShorelineSupport K n ≤ bellmanShorelineSupport L n + h * ‖n‖ := by
  apply csSup_le (hKne.image _)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hsub hx
  have hySupport : inner ℝ n y ≤ bellmanShorelineSupport L n :=
    le_csSup
      (hLcompact.bddAbove_image (continuous_const.inner continuous_id).continuousOn)
      ⟨y, hy, rfl⟩
  calc
    inner ℝ n x = inner ℝ n y + inner ℝ n (x - y) := by
      rw [inner_sub_right, add_sub_cancel]
    _ ≤ bellmanShorelineSupport L n + ‖n‖ * ‖x - y‖ :=
      add_le_add hySupport (real_inner_le_norm _ _)
    _ ≤ bellmanShorelineSupport L n + ‖n‖ * h :=
      add_le_add_right (mul_le_mul_of_nonneg_left hxy (norm_nonneg n)) _
    _ = bellmanShorelineSupport L n + h * ‖n‖ := by ring

/-- Unit-normal form of conservative polygonal support estimate. -/
theorem bellmanShorelineSupport_sub_le_polygonalSupport
    {K L : Set F} {h : ℝ} (hKne : K.Nonempty)
    (hLcompact : IsCompact L)
    (hsub : K ⊆ bellmanShorelineThickening L h)
    {n : F} (hn : ‖n‖ = 1) :
    bellmanShorelineSupport K n - h ≤ bellmanShorelineSupport L n := by
  have hle := bellmanShorelineSupport_le_of_subset_thickening
    hKne hLcompact hsub n
  rw [hn, mul_one] at hle
  linarith

end GaloisForLFunctions.HTGeometry

end
