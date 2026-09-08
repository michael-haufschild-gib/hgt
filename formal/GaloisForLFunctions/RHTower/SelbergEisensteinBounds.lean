import GaloisForLFunctions.RHTower.SelbergPowerCurvature

/-!
# Original Eisenstein derivative and curvature bounds

Positive original summands dominate the differentiated Poincare series. The
resulting global gradient bound controls the actual negative-power curvature
by the same amplitude. The original vertical derivative also supplies a
uniform decaying envelope for the actual top current.
-/

open Set Filter Topology UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergEisensteinBounds
open _root_.RHTower SelbergPositiveEisenstein SelbergEisensteinPlane SelbergPowerCurvature
  SelbergMaassTraceEnergy SelbergMaassMean
noncomputable section

private theorem seed_norm (z : D4BMUpperHalfPlaneCoordinate) (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeed z parameter.s p‖ = seed z p := by
  rw [seed_complex, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- Original positive summands dominate the real part of every absolutely bounded derivative series. -/
theorem half_sum_bound (z : D4BMUpperHalfPlaneCoordinate) (g : D4BMPrimitiveIntegerPair → ℂ) (C : ℝ)
    (hb : ∀ p, ‖g p‖ ≤ C * seed z p) :
    |((1 / 2 : ℂ) * ∑' p, g p).re| ≤ C * E z := by
  have hm := (seed_summable z).mul_left C
  have hg : Summable g := Summable.of_norm_bounded hm hb
  calc
    _ ≤ ‖(1 / 2 : ℂ) * ∑' p, g p‖ := Complex.abs_re_le_norm _
    _ = (1 / 2 : ℝ) * ‖∑' p, g p‖ := by rw [norm_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * ∑' p, ‖g p‖ := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hg.norm) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (∑' p, C * seed z p) :=
      mul_le_mul_of_nonneg_left (hg.norm.tsum_le_tsum hb hm) (by norm_num)
    _ = (1 / 2 : ℝ) * (C * ∑' p, seed z p) := by rw [tsum_mul_left]
    _ = C * E z := by rw [E_eq]; ring

/-- Actual horizontal Eisenstein derivatives satisfy a global original-value bound. -/
theorem Ex_bound (z : D4BMUpperHalfPlaneCoordinate) : |Ex z| ≤ (4 / z.y) * E z := by
  apply half_sum_bound
  intro p
  have h := norm_d4BMPoincareSeedHorizontalFirstJet_le z parameter.s p
  rw [seed_norm] at h
  norm_num [parameter] at h ⊢
  exact h

/-- Actual vertical Eisenstein derivatives satisfy a global original-value bound. -/
theorem Ey_bound (z : D4BMUpperHalfPlaneCoordinate) : |Ey z| ≤ (6 / z.y) * E z := by
  apply half_sum_bound
  intro p
  have h := norm_d4BMPoincareSeedVerticalFirstJet_le z parameter.s p
  rw [seed_norm] at h
  norm_num [parameter] at h ⊢
  exact h

/-- The full original planar gradient has a global hyperbolic logarithmic bound. -/
theorem plane_gradient_bound {z : ℂ} (hz : 0 < z.im) :
    z.im ^ 2 * (dir 1 planeE z ^ 2 + dir Complex.I planeE z ^ 2) ≤ 52 * planeE z ^ 2 := by
  let w : D4BMUpperHalfPlaneCoordinate := ⟨z.re, z.im, hz⟩
  have hp : point w.x w.y = z := by apply Complex.ext <;> simp [point, w]
  have hx := Ex_bound w
  have hy := Ey_bound w
  rw [← planeE_dir_one, ← planeE_eq, hp] at hx
  rw [← planeE_dir_I, ← planeE_eq, hp] at hy
  change |dir 1 planeE z| ≤ 4 / z.im * planeE z at hx
  change |dir Complex.I planeE z| ≤ 6 / z.im * planeE z at hy
  have hxm : |dir 1 planeE z| * z.im ≤ 4 * planeE z := by
    have h : |dir 1 planeE z| ≤ (4 * planeE z) / z.im := by convert hx using 1; ring
    exact (le_div_iff₀ hz).mp h
  have hym : |dir Complex.I planeE z| * z.im ≤ 6 * planeE z := by
    have h : |dir Complex.I planeE z| ≤ (6 * planeE z) / z.im := by convert hy using 1; ring
    exact (le_div_iff₀ hz).mp h
  have hpos := planeE_pos hz
  have hxs := (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hz.le) (by positivity : 0 ≤ 4 * planeE z)).mpr hxm
  have hys := (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hz.le) (by positivity : 0 ≤ 6 * planeE z)).mpr hym
  simp only [mul_pow, sq_abs] at hxs hys
  nlinarith

/-- A finite explicit amplitude multiple dominates all original model curvature. -/
def curvatureConstant (lam : Ioi (0 : ℝ)) : ℝ :=
  52 * ((lam : ℝ) / 4) * ((lam : ℝ) / 4 + 1) + (lam : ℝ) / 2

/-- The original model's curvature is globally dominated by its original amplitude. -/
theorem curvature_le_model (lam : Ioi (0 : ℝ)) {z : ℂ} (hz : 0 < z.im) :
    curvature lam z ≤ curvatureConstant lam * model lam z := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  have hp := planeE_pos hz
  have hm := mul_le_mul_of_nonneg_left (plane_gradient_bound hz)
    (show 0 ≤ ((lam : ℝ) / 4) * ((lam : ℝ) / 4 + 1) * planeE z ^ (-(lam : ℝ) / 4 - 2) by positivity)
  have he : planeE z ^ (-(lam : ℝ) / 4 - 2) * planeE z ^ 2 = model lam z := by
    rw [model, show -(lam : ℝ) / 4 - 2 = (-(lam : ℝ) / 4 - 1) - 1 by ring,
      Real.rpow_sub_one hp.ne', Real.rpow_sub_one hp.ne']
    field_simp [hp.ne']
  rw [curvature_eq lam hz]
  calc
    _ ≤ (((lam : ℝ) / 4) * ((lam : ℝ) / 4 + 1) * planeE z ^ (-(lam : ℝ) / 4 - 2)) *
        (52 * planeE z ^ 2) + (lam : ℝ) / 2 * model lam z := by nlinarith only [hm]
    _ = curvatureConstant lam * model lam z := by
      unfold curvatureConstant
      rw [show (((lam : ℝ) / 4) * ((lam : ℝ) / 4 + 1) * planeE z ^ (-(lam : ℝ) / 4 - 2)) *
        (52 * planeE z ^ 2) = 52 * ((lam : ℝ) / 4) * ((lam : ℝ) / 4 + 1) *
          (planeE z ^ (-(lam : ℝ) / 4 - 2) * planeE z ^ 2) by ring, he]
      ring

/-- The actual vertical model current is controlled by its original amplitude and height. -/
theorem model_vertical_bound (lam : Ioi (0 : ℝ)) {z : ℂ} (hz : 0 < z.im) :
    |dir Complex.I (model lam) z| ≤ (3 * (lam : ℝ) / 2) * model lam z / z.im := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  have hp := planeE_pos hz
  let w : D4BMUpperHalfPlaneCoordinate := ⟨z.re, z.im, hz⟩
  have hw : point w.x w.y = z := by apply Complex.ext <;> simp [point, w]
  have hy := Ey_bound w
  rw [← planeE_dir_I, ← planeE_eq, hw] at hy
  change |dir Complex.I planeE z| ≤ (6 / z.im) * planeE z at hy
  have hd := ((contDiffOn_infty.mp planeE_contDiffOn) 2).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hr := rpow_dir (hd.differentiableAt (by norm_num)) hp (-(lam : ℝ) / 4) Complex.I
  change dir Complex.I (model lam) z = _ at hr
  rw [hr, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  have ha : |-(lam : ℝ) / 4| = (lam : ℝ) / 4 := by
    rw [abs_div, abs_neg, abs_of_pos hl]
    norm_num
  rw [ha]
  calc
    _ ≤ ((lam : ℝ) / 4) * planeE z ^ (-(lam : ℝ) / 4 - 1) * ((6 / z.im) * planeE z) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    _ = (3 * (lam : ℝ) / 2) * model lam z / z.im := by
      rw [Real.rpow_sub_one hp.ne', model]
      field_simp [hp.ne', hz.ne']
      ring

/-- A uniform explicit vanishing-height envelope bounds the actual top current pointwise. -/
theorem model_vertical_le_height (lam : Ioi (0 : ℝ)) (z : D4BMUpperHalfPlaneCoordinate) :
    |dir Complex.I (model lam) (point z.x z.y)| ≤
      (3 * (lam : ℝ) / 2) * z.y ^ (-(lam : ℝ) / 2 - 1) := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  have h := model_vertical_bound lam (z := point z.x z.y) (by simpa [point] using z.y_pos)
  have hi : (point z.x z.y).im = z.y := by simp [point]
  rw [hi] at h
  calc
    _ ≤ (3 * (lam : ℝ) / 2) * model lam (point z.x z.y) / z.y := h
    _ ≤ (3 * (lam : ℝ) / 2) * z.y ^ (-(lam : ℝ) / 2) / z.y :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (model_le_height lam z) (by positivity)) z.y_pos.le
    _ = _ := by rw [Real.rpow_sub_one z.y_pos.ne']; ring

end
end GaloisForLFunctions.RHTower.SelbergEisensteinBounds
