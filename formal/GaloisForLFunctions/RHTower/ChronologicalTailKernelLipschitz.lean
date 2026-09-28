import GaloisForLFunctions.RHTower.ChronologicalTailKernelAnalytic

/-!
# The Bose defect is Lipschitz on `(0, 2]`

The defect `h(t) = 1/t - 1/(eᵗ - 1)` is the restriction to the positive axis of the kernel
`boseKernelE`, which is analytic on the strip `|Im z| < 2π`.  Its derivative is therefore bounded
on the compact convex disc `|z - 1| ≤ 1` inside the strip, and the mean value inequality on that
disc gives a Lipschitz bound for `h` on `(0, 2]`, uniform up to the removable singularity at `0`.
-/

open Set Metric
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-- **The Bose defect is Lipschitz on `(0, 2]`.** -/
theorem exists_fusionBoseDefect_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Ioc (0 : ℝ) 2, ∀ t ∈ Ioc (0 : ℝ) 2,
      |fusionBoseDefect s - fusionBoseDefect t| ≤ L * |s - t| := by
  set D : Set ℂ := closedBall (1 : ℂ) 1 with hD
  have hDstrip : D ⊆ boseStrip := by
    intro z hz
    have h1 : ‖z - 1‖ ≤ 1 := by simpa [hD, dist_eq_norm] using hz
    have him : |z.im| ≤ ‖z - 1‖ := by
      simpa using Complex.abs_im_le_norm (z - 1)
    have hpi : 3 < Real.pi := Real.pi_gt_three
    exact mem_boseStrip.mpr (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn
    ((boseKernelE_analyticOnNhd.deriv.continuousOn).mono hDstrip)
  refine ⟨max M 0, le_max_right _ _, fun s hs t ht => ?_⟩
  have hmem : ∀ r ∈ Ioc (0 : ℝ) 2, (r : ℂ) ∈ D := by
    intro r hr
    rw [hD, mem_closedBall, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hr.1, hr.2]
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => boseKernelE_differentiableOn.differentiableAt
      (isOpen_boseStrip.mem_nhds (hDstrip hz)))
    (fun z hz => (hM z hz).trans (le_max_left M 0)) (convex_closedBall (1 : ℂ) 1)
    (hmem t ht) (hmem s hs)
  rw [boseKernelE_ofReal hs.1, boseKernelE_ofReal ht.1, ← Complex.ofReal_sub,
    ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at hmv
  exact hmv

end RHTower
