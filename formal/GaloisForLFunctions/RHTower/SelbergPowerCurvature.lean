import GaloisForLFunctions.RHTower.SelbergEisensteinPlane

/-!
# Actual curvature of negative powers of the positive Eisenstein series

The literal positive Eisenstein series at s=2 supplies the smooth source and its
actual Frechet eigen-equation. For every positive lambda, its negative lambda/4
power has strictly positive positive-sign hyperbolic curvature and a uniform
vanishing cusp envelope. The exact power rule retains the gradient square.
These scalar functions are not asserted to be Maass eigenforms.
-/

open Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergPowerCurvature
open _root_.RHTower SelbergPositiveEisenstein SelbergEisensteinPlane SelbergMaassTraceEnergy SelbergMaassMean
noncomputable section

/-- Exact real-power chain rule for one actual planar derivative. -/
theorem rpow_dir {F : ℂ → ℝ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (hp : 0 < F z) (r : ℝ) (v : ℂ) :
    dir v (fun w => F w ^ r) z = r * F z ^ (r - 1) * dir v F z := by
  have h := congrArg (fun L => L v) (hF.hasFDerivAt.rpow_const (p := r) (Or.inl hp.ne')).fderiv
  exact h

/-- The actual second derivative retains both the gradient square and the source second derivative. -/
theorem rpow_second_dir {F : ℂ → ℝ} {z : ℂ} (hF : ContDiffAt ℝ 2 F z) (hp : 0 < F z) (r : ℝ) (v : ℂ) :
    dir v (dir v (fun w => F w ^ r)) z =
      r * (r - 1) * F z ^ (r - 2) * dir v F z ^ 2 +
        r * F z ^ (r - 1) * dir v (dir v F) z := by
  have he : dir v (fun w => F w ^ r) =ᶠ[𝓝 z] (fun w => r * F w ^ (r - 1) * dir v F w) := by
    filter_upwards [hF.eventually (by norm_num), hF.continuousAt.eventually (eventually_gt_nhds hp)] with w hw hwp
    exact rpow_dir (hw.differentiableAt (by norm_num)) hwp r v
  have hd := (dir_contDiffAt hF v).differentiableAt (by norm_num)
  have hf := hF.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hpow := hf.hasFDerivAt.rpow_const (p := r - 1) (Or.inl hp.ne')
  have hh := congrArg (fun L => L v) ((hpow.const_mul r).mul hd.hasFDerivAt).fderiv
  change fderiv ℝ (dir v (fun w => F w ^ r)) z v = _
  rw [he.fderiv_eq]
  change dir v (fun w => r * F w ^ (r - 1) * dir v F w) z = _
  change dir v (fun w => r * F w ^ (r - 1) * dir v F w) z =
    r * F z ^ (r - 1) * dir v (dir v F) z + dir v F z * (r * ((r - 1) * F z ^ (r - 1 - 1) * dir v F z)) at hh
  rw [hh]
  rw [show r - 1 - 1 = r - 2 by ring]
  ring

/-- The complete planar Laplacian chain rule for a positive C² source. -/
theorem rpow_laplacian {F : ℂ → ℝ} {z : ℂ} (hF : ContDiffAt ℝ 2 F z) (hp : 0 < F z) (r : ℝ) :
    realLaplacian (fun w => F w ^ r) z =
      r * (r - 1) * F z ^ (r - 2) * (dir 1 F z ^ 2 + dir Complex.I F z ^ 2) +
        r * F z ^ (r - 1) * realLaplacian F z := by
  unfold realLaplacian
  rw [rpow_second_dir hF hp, rpow_second_dir hF hp]
  ring

/-- A literal negative power of the original smooth positive Eisenstein function. -/
def model (lam : Ioi (0 : ℝ)) (z : ℂ) : ℝ := planeE z ^ (-(lam : ℝ) / 4)

/-- The scalar model is smooth throughout the upper half-plane. -/
theorem model_contDiffOn (lam : Ioi (0 : ℝ)) : ContDiffOn ℝ ∞ (model lam) {z : ℂ | 0 < z.im} :=
  planeE_contDiffOn.rpow_const_of_ne (fun _ hz => (planeE_pos hz).ne')

/-- Every actual model value at positive height is positive. -/
theorem model_pos (lam : Ioi (0 : ℝ)) {z : ℂ} (hz : 0 < z.im) : 0 < model lam z :=
  Real.rpow_pos_of_pos (planeE_pos hz) _

/-- The original modular translation acts trivially on the actual model. -/
theorem model_translate (lam : Ioi (0 : ℝ)) (z : D4BMUpperHalfPlaneCoordinate) :
    model lam (point (z.x + 1) z.y) = model lam (point z.x z.y) := by
  unfold model
  change planeE (point (d4BMEisensteinTranslateCoordinate z).x (d4BMEisensteinTranslateCoordinate z).y) ^
    (-(lam : ℝ) / 4) = _
  rw [planeE_eq (d4BMEisensteinTranslateCoordinate z), planeE_eq z, E_translate]

/-- The original modular inversion acts trivially on the actual model. -/
theorem model_invert (lam : Ioi (0 : ℝ)) (z : D4BMUpperHalfPlaneCoordinate) :
    model lam (point (d4BMEisensteinInvertCoordinate z).x (d4BMEisensteinInvertCoordinate z).y) =
      model lam (point z.x z.y) := by
  unfold model
  rw [planeE_eq, planeE_eq, E_invert]

/-- Literal positive-sign hyperbolic curvature, using the actual Frechet Laplacian. -/
def curvature (lam : Ioi (0 : ℝ)) (z : ℂ) : ℝ :=
  z.im ^ 2 * realLaplacian (model lam) z + (lam : ℝ) * model lam z

/-- Exact curvature decomposition: a nonnegative gradient square plus positive amplitude mass. -/
theorem curvature_eq (lam : Ioi (0 : ℝ)) {z : ℂ} (hz : 0 < z.im) :
    curvature lam z =
      ((lam : ℝ) / 4) * ((lam : ℝ) / 4 + 1) * planeE z ^ (-(lam : ℝ) / 4 - 2) *
        z.im ^ 2 * (dir 1 planeE z ^ 2 + dir Complex.I planeE z ^ 2) +
      (lam : ℝ) / 2 * model lam z := by
  have hc := ((contDiffOn_infty.mp planeE_contDiffOn) 2).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hz)
  have he := planeE_eigen_equation hz
  have hp := planeE_pos hz
  have hL := rpow_laplacian hc hp (-(lam : ℝ) / 4)
  change realLaplacian (model lam) z = _ at hL
  unfold curvature
  rw [hL]
  rw [Real.rpow_sub_one hp.ne']
  dsimp only [model]
  field_simp [hp.ne']
  simp only [neg_div] at *
  linear_combination (-8 * (lam : ℝ) * planeE z ^ (-((lam : ℝ) / 4))) * he

/-- For every positive parameter the actual model has strictly positive hyperbolic curvature. -/
theorem curvature_pos (lam : Ioi (0 : ℝ)) {z : ℂ} (hz : 0 < z.im) : 0 < curvature lam z := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  have hp := planeE_pos hz
  rw [curvature_eq lam hz]
  have ha := model_pos lam hz
  have hg : 0 ≤ dir 1 planeE z ^ 2 + dir Complex.I planeE z ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hterm : 0 ≤ ((lam : ℝ) / 4) * ((lam : ℝ) / 4 + 1) * planeE z ^ (-(lam : ℝ) / 4 - 2) *
      z.im ^ 2 * (dir 1 planeE z ^ 2 + dir Complex.I planeE z ^ 2) := by positivity
  exact add_pos_of_nonneg_of_pos hterm (mul_pos (by positivity) ha)

/-- The original identity-row lower bound gives an explicit vanishing cusp envelope. -/
theorem model_le_height (lam : Ioi (0 : ℝ)) (z : D4BMUpperHalfPlaneCoordinate) :
    model lam (point z.x z.y) ≤ z.y ^ (-(lam : ℝ) / 2) := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  unfold model
  rw [planeE_eq]
  have h := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos z.y_pos) (height_sq_le z)
    (show -(lam : ℝ) / 4 ≤ 0 by linarith)
  have he : (z.y ^ 2) ^ (-(lam : ℝ) / 4) = z.y ^ (-(lam : ℝ) / 2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul z.y_pos.le]
    congr 1
    ring
  exact h.trans_eq he

/-- The actual scalar model decays uniformly at the cusp for every positive parameter. -/
theorem model_cusp_decay (lam : Ioi (0 : ℝ)) {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : D4BMUpperHalfPlaneCoordinate, Y ≤ z.y → model lam (point z.x z.y) < eps := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  have ht : Tendsto (fun y : ℝ => y ^ (-(lam : ℝ) / 2)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (y := (lam : ℝ) / 2) (by positivity)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (ht.eventually_lt_const heps)
  refine ⟨max Y 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z hz => ?_⟩
  exact lt_of_le_of_lt (model_le_height lam z) (hY z.y ((le_max_left _ _).trans hz))

end
end GaloisForLFunctions.RHTower.SelbergPowerCurvature
