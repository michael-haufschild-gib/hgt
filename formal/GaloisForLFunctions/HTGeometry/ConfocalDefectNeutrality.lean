import GaloisForLFunctions.HTGeometry.ConfocalAbelDefectFlow

/-!
# Cofinal transverse neutrality and confocal selection

For a bounded source, convergence of the nodes to the origin is stronger than finite-packet
selection needs.  The intrinsic hypothesis is cofinal vanishing of `|z| - re z`.  A pointwise
linear comparison transports this transverse neutrality to every confocal scale beyond the source
radius.
-/

open Complex Filter Topology

namespace HTGeometry

noncomputable section

/-- On a radius-`M` disk and beyond the radial threshold, the confocal defect is linearly
controlled by the transverse defect. -/
theorem confocalDefect_le_scale_mul_transverseDefect
    {M R : ℝ} (hM : 0 ≤ M) (hRM : M < R) {z : ℂ} (hz : ‖z‖ ≤ M) :
    confocalDefect R z ≤ R / (R - M) * transverseDefect z := by
  let x : ℝ := z.re
  let y : ℝ := z.im
  let r : ℝ := ‖z‖
  let a : ℝ := R - x
  let s : ℝ := ‖(R : ℂ) - z‖
  have hr0 : 0 ≤ r := norm_nonneg z
  have hxle : x ≤ r := by
    dsimp only [x, r]
    exact Complex.re_le_norm z
  have hrM : r ≤ M := hz
  have ha0 : 0 < a := by
    dsimp only [a, x]
    linarith
  have hRM0 : 0 < R - M := sub_pos.mpr hRM
  have hsa : a ≤ s := by
    dsimp only [a, s, x]
    simpa using Complex.re_le_norm ((R : ℂ) - z)
  have hs0 : 0 ≤ s := norm_nonneg _
  have hrSq : r ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp only [r, x, y]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsSq : s ^ 2 = a ^ 2 + y ^ 2 := by
    dsimp only [s, a, x, y]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im]
    ring
  have htrans0 : 0 ≤ r - x := sub_nonneg.mpr hxle
  have hsum : r + x ≤ 2 * M := by
    have hxr : x ≤ r := hxle
    linarith
  have hySq : y ^ 2 = (r - x) * (r + x) := by
    nlinarith
  have hySq_le : y ^ 2 ≤ 2 * M * (r - x) := by
    rw [hySq]
    nlinarith [mul_nonneg htrans0 (sub_nonneg.mpr hsum)]
  have hden : 0 < s + a := by positivity
  have hgap : s - a = y ^ 2 / (s + a) := by
    apply (eq_div_iff hden.ne').2
    nlinarith
  have hdenLower : 2 * (R - M) ≤ s + a := by
    have haLower : R - M ≤ a := by
      dsimp only [a, x]
      linarith
    linarith
  have hgap_le : s - a ≤ M / (R - M) * (r - x) := by
    rw [hgap]
    have hdiv : y ^ 2 / (s + a) ≤ y ^ 2 / (2 * (R - M)) :=
      div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) hdenLower
    have hnum : y ^ 2 / (2 * (R - M)) ≤
        M / (R - M) * (r - x) := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * (R - M))]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      field_simp [hRM0.ne']
      nlinarith
    exact hdiv.trans hnum
  have hrewrite : confocalDefect R z = (r - x) + (s - a) := by
    rw [confocalDefect]
    dsimp only [r, x, s, a]
    ring
  rw [hrewrite, transverseDefect]
  change (r - x) + (s - a) ≤ R / (R - M) * (r - x)
  have hfactor : 1 + M / (R - M) = R / (R - M) := by
    field_simp [hRM0.ne']
    ring
  calc
    (r - x) + (s - a) ≤ (r - x) + M / (R - M) * (r - x) :=
      add_le_add le_rfl hgap_le
    _ = (1 + M / (R - M)) * (r - x) := by ring
    _ = R / (R - M) * (r - x) := by rw [hfactor]

/-- Cofinal vanishing of the transverse defect implies cofinal vanishing of the confocal defect
at every fixed scale beyond the source radius. -/
theorem tendsto_confocalDefect_cofinite_zero_of_transverseDefect
    {I : Type*} {z : I → ℂ} {M R : ℝ}
    (hM : 0 ≤ M) (hRM : M < R) (hbound : ∀ i, ‖z i‖ ≤ M)
    (htrans : Tendsto (fun i => transverseDefect (z i)) cofinite (nhds 0)) :
    Tendsto (fun i => confocalDefect R (z i)) cofinite (nhds 0) := by
  have hscale : Tendsto
      (fun i : I => R / (R - M) * transverseDefect (z i))
      cofinite (nhds 0) := by
    simpa using htrans.const_mul (R / (R - M))
  exact squeeze_zero'
    (Eventually.of_forall fun i => confocalDefect_nonneg (z i))
    (Eventually.of_forall fun i =>
      confocalDefect_le_scale_mul_transverseDefect hM hRM (hbound i))
    hscale

/-- The threshold `R>M` is optimal uniformly over the positively oriented source class.  Below
the source radius, the positive real endpoint has zero transverse defect but superunit normalized
affine amplitude. -/
theorem below_radius_positive_node_has_zero_defect_and_superunit_amplitude
    {M R : ℝ} (hR : 0 < R) (hRM : R < M) :
    transverseDefect (M : ℂ) = 0 ∧
      1 < ‖(M : ℂ) / (R : ℂ)‖ + ‖1 - (M : ℂ) / (R : ℂ)‖ := by
  have hM : 0 < M := hR.trans hRM
  constructor
  · rw [transverseDefect, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hM, Complex.ofReal_re]
    ring
  · rw [affineAmplitude_eq_one_add_confocalDefect_div hR]
    have hdefect : confocalDefect R (M : ℂ) = 2 * (M - R) := by
      rw [confocalDefect, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
      have hsub : (R : ℂ) - (M : ℂ) = ((R - M : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (sub_neg.mpr hRM)]
      ring
    rw [hdefect]
    exact lt_add_of_pos_right 1 (div_pos (by positivity) hR)

end

end HTGeometry
