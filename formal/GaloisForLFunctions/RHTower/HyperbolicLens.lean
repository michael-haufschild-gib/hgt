import GaloisForLFunctions.RHTower.HyperbolicBallMeanValue
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMWeightedResponseAdmission

open MeasureTheory UpperHalfPlane Metric Set
open scoped MatrixGroups

/-!
# Intersections of hyperbolic balls

Moving two centres to `i/a` and `ia` (`exists_normalize`), the identity
`cosh d(w, ia) + cosh d(w, i/a) = (a + 1/a) cosh d(w, i)` (`cosh_dist_add_cosh_dist`) puts the intersection
of the two radius-`R` balls inside the ball about the midpoint on which `cosh d ≤ cosh R / cosh(D/2)`.
With `vol B_r(i) ≤ 8 eʳ` this gives `vol(B_R(z) ∩ B_R(z')) ≤ 16 cosh R / cosh(d(z,z')/2)` (`volume_lens_le`).
-/

namespace GaloisForLFunctions.RHTower.HyperbolicLens

open GaloisForLFunctions.RHTower.HyperbolicRotationMean
open GaloisForLFunctions.RHTower.HyperbolicPointPair
open GaloisForLFunctions.RHTower.HyperbolicPointPairCentre

/-- `cosh d(w, it) = (x² + y² + t²)/(2yt)`. -/
theorem cosh_dist_axis (w : ℍ) {t : ℝ} (ht : 0 < t) :
    Real.cosh (dist w (axisPoint ht)) = (w.re ^ 2 + w.im ^ 2 + t ^ 2) / (2 * w.im * t) := by
  rw [cosh_dist]
  have hw := w.im_pos
  have him : (axisPoint ht).im = t := by simp [axisPoint, UpperHalfPlane.im]
  have hre : ((axisPoint ht : ℍ) : ℂ) = Complex.I * t := rfl
  rw [him, Complex.dist_eq, hre, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp
  ring

/-- **Three-point identity.** `cosh d(w, ia) + cosh d(w, i/a) = (a + 1/a) cosh d(w, i)`. -/
theorem cosh_dist_add_cosh_dist (w : ℍ) {a : ℝ} (ha : 0 < a) :
    Real.cosh (dist w (axisPoint ha)) + Real.cosh (dist w (axisPoint (inv_pos.mpr ha))) =
      (a + 1 / a) * Real.cosh (dist w (axisPoint one_pos)) := by
  rw [cosh_dist_axis, cosh_dist_axis, cosh_dist_axis]
  have hw := w.im_pos
  field_simp
  ring

/-- The diagonal element `diag(α, α⁻¹)`, acting by `w ↦ α² w`. -/
noncomputable def scaleSL {α : ℝ} (hα : 0 < α) : SL(2, ℝ) :=
  ⟨!![α, 0; 0, α⁻¹], by simp [Matrix.det_fin_two_of, hα.ne']⟩

theorem scaleSL_axis {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 0 < t) :
    scaleSL hα • axisPoint ht = axisPoint (mul_pos (pow_pos hα 2) ht) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp only [scaleSL, axisPoint, UpperHalfPlane.coe_mk, Algebra.algebraMap_self, RingHom.id_apply]
  simp
  field_simp

theorem rotSL_axis {t : ℝ} (ht : 0 < t) :
    rotSL (Real.pi / 2) • axisPoint ht = axisPoint (inv_pos.mpr ht) := by
  rw [← rot_smul_eq]
  apply UpperHalfPlane.ext
  rw [coe_rot_smul, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp only [axisPoint, UpperHalfPlane.coe_mk, Complex.ofReal_zero, Complex.ofReal_one, mul_zero,
    zero_add, mul_one, add_zero]
  have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  push_cast
  rw [Complex.I_sq]
  ring_nf
  simp [this]

theorem axisPoint_one : axisPoint one_pos = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext; simp [axisPoint]

theorem rotSL_I (θ : ℝ) : rotSL θ • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [← rot_smul_eq]; exact rot_smul_I θ

/-- Any two points can be moved by `SL(2,ℝ)` to `i/a` and `ia` with `a ≥ 1`. -/
theorem exists_normalize (z z' : ℍ) :
    ∃ g : SL(2, ℝ), ∃ a : ℝ, ∃ ha : 0 < a, 1 ≤ a ∧
      g • z = axisPoint (inv_pos.mpr ha) ∧ g • z' = axisPoint ha := by
  -- move `z` to `i`
  set g₁ := (toSL2R z)⁻¹
  have hz : g₁ • z = UpperHalfPlane.I := by
    rw [inv_smul_eq_iff]; exact (toSL2R_smul_I z).symm
  obtain ⟨θ, y, hy, hu⟩ := exists_rot_axis (g₁ • z')
  set g₂ := rotSL (-θ) * g₁
  have hz2 : g₂ • z = UpperHalfPlane.I := by rw [mul_smul, hz, rotSL_I]
  have hz2' : g₂ • z' = axisPoint hy := by
    rw [mul_smul, hu, ← rot_smul_eq]; exact rot_neg_smul θ _
  -- arrange `y ≥ 1`
  obtain ⟨g₃, b, hb, hb1, h3z, h3z'⟩ : ∃ g₃ : SL(2, ℝ), ∃ b : ℝ, ∃ hb : 0 < b, 1 ≤ b ∧
      g₃ • z = UpperHalfPlane.I ∧ g₃ • z' = axisPoint hb := by
    by_cases hy1 : 1 ≤ y
    · exact ⟨g₂, y, hy, hy1, hz2, hz2'⟩
    · refine ⟨rotSL (Real.pi / 2) * g₂, y⁻¹, inv_pos.mpr hy, ?_, ?_, ?_⟩
      · rw [one_le_inv₀ hy]; linarith
      · rw [mul_smul, hz2, rotSL_I]
      · rw [mul_smul, hz2', rotSL_axis]
  -- scale by `b^{-1/2}`
  set a := Real.sqrt b
  have ha : 0 < a := Real.sqrt_pos.mpr hb
  have ha1 : 1 ≤ a := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hb1
  set α := (Real.sqrt a)⁻¹
  have hα : 0 < α := inv_pos.mpr (Real.sqrt_pos.mpr ha)
  have hα2 : α ^ 2 = a⁻¹ := by
    simp only [α, inv_pow, Real.sq_sqrt ha.le]
  refine ⟨scaleSL hα * g₃, a, ha, ha1, ?_, ?_⟩
  · rw [mul_smul, h3z, ← axisPoint_one, scaleSL_axis]
    congr 1; rw [hα2, mul_one]
  · rw [mul_smul, h3z', scaleSL_axis]
    congr 1
    rw [hα2, show b = a ^ 2 by simp [a, Real.sq_sqrt hb.le]]
    field_simp

theorem dist_axis_inv {a : ℝ} (ha : 0 < a) (ha1 : 1 ≤ a) :
    dist (axisPoint (inv_pos.mpr ha)) (axisPoint ha) = 2 * Real.log a := by
  rw [dist_of_re_eq (by simp [axisPoint, UpperHalfPlane.re])]
  have h1 : (axisPoint (inv_pos.mpr ha)).im = a⁻¹ := by simp [axisPoint, UpperHalfPlane.im]
  have h2 : (axisPoint ha).im = a := by simp [axisPoint, UpperHalfPlane.im]
  rw [h1, h2, Real.log_inv, Real.dist_eq]
  have := Real.log_nonneg ha1
  rw [abs_of_nonpos (by linarith)]
  ring

theorem cosh_log {a : ℝ} (ha : 0 < a) : Real.cosh (Real.log a) = (a + 1 / a) / 2 := by
  rw [Real.cosh_eq, Real.exp_log ha, Real.exp_neg, Real.exp_log ha, one_div]

theorem cosh_le_of_dist_le {w z : ℍ} {R : ℝ} (h : dist w z ≤ R) :
    Real.cosh (dist w z) ≤ Real.cosh R := by
  rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg]
  exact h.trans (le_abs_self R)

theorem dist_le_log_of_cosh_le {d C : ℝ} (hC : 0 < C) (h : Real.cosh d ≤ C) :
    d ≤ Real.log (2 * C) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_pos (-d)
  rw [Real.cosh_eq] at h
  linarith

/-- **Lens bound.** Two hyperbolic balls of radius `R` whose centres are at distance `D` meet in a set
of hyperbolic area at most `16 cosh R / cosh(D/2)`. -/
theorem volume_lens_le (z z' : ℍ) (R : ℝ) :
    volume (closedBall z R ∩ closedBall z' R) ≤
      ENNReal.ofReal (16 * Real.cosh R / Real.cosh (dist z z' / 2)) := by
  obtain ⟨g, a, ha, ha1, hgz, hgz'⟩ := exists_normalize z z'
  have hD : dist z z' = 2 * Real.log a := by
    rw [← dist_smul g z z', hgz, hgz', dist_axis_inv ha ha1]
  set C := 2 * Real.cosh R / (a + 1 / a)
  have hapos : 0 < a + 1 / a := by positivity
  have hC : 0 < C := div_pos (by positivity) hapos
  set A : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.toGL g
  have hpre : closedBall z R ∩ closedBall z' R =
      (fun w => A • w) ⁻¹' (closedBall (g • z) R ∩ closedBall (g • z') R) := by
    ext w
    simp only [mem_inter_iff, mem_closedBall, mem_preimage]
    change _ ↔ dist (g • w) (g • z) ≤ R ∧ dist (g • w) (g • z') ≤ R
    rw [dist_smul, dist_smul]
  have hsub : closedBall (g • z) R ∩ closedBall (g • z') R ⊆
      closedBall UpperHalfPlane.I (Real.log (2 * C)) := by
    rintro w ⟨h1, h2⟩
    rw [mem_closedBall] at h1 h2 ⊢
    rw [hgz] at h1; rw [hgz'] at h2
    have hsum := cosh_dist_add_cosh_dist w ha
    rw [axisPoint_one] at hsum
    have hc : Real.cosh (dist w UpperHalfPlane.I) ≤ C := by
      rw [le_div_iff₀ hapos]
      nlinarith [cosh_le_of_dist_le h1, cosh_le_of_dist_le h2]
    exact dist_le_log_of_cosh_le hC hc
  rw [hpre, measure_preimage_smul]
  calc volume (closedBall (g • z) R ∩ closedBall (g • z') R)
      ≤ volume (closedBall UpperHalfPlane.I (Real.log (2 * C))) := measure_mono hsub
    _ ≤ ENNReal.ofReal (8 * Real.exp (Real.log (2 * C))) :=
        RHTower.D4BMModularCore.hyperbolic_ball_volume_le _
    _ = ENNReal.ofReal (16 * Real.cosh R / Real.cosh (dist z z' / 2)) := by
        congr 1
        rw [Real.exp_log (by positivity), hD, show 2 * Real.log a / 2 = Real.log a by ring,
          cosh_log ha]
        simp only [C]
        field_simp
        ring

end GaloisForLFunctions.RHTower.HyperbolicLens
