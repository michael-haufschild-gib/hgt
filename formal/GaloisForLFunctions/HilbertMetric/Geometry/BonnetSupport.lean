import GaloisForLFunctions.HTGeometry.GaussBonnetPlanarPartials

/-!
# Stereographic support-function calculus

The conformal factor of the round sphere is `2/(1+x²+y²)`.
Differentiating the support function `1 + ε U/(1+x²+y²)` gives a radius
matrix whose trace-free part is a scalar multiple of the
Euclidean Hessian's trace-free part.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.BonnetSupport
open GaloisForLFunctions.HTGeometry.GaussBonnet
noncomputable section

private theorem px_mul {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : ℝ × ℝ) : px (fun q => f q * g q) p = px f p * g p + f p * px g p :=
  (hasDerivAt_px (hf.mul hg) p.1 p.2).unique
    ((hasDerivAt_px hf p.1 p.2).mul (hasDerivAt_px hg p.1 p.2))

private theorem py_mul {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : ℝ × ℝ) : py (fun q => f q * g q) p = py f p * g p + f p * py g p :=
  (hasDerivAt_py (hf.mul hg) p.1 p.2).unique
    ((hasDerivAt_py hf p.1 p.2).mul (hasDerivAt_py hg p.1 p.2))

private theorem px_add {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : ℝ × ℝ) : px (fun q => f q + g q) p = px f p + px g p :=
  (hasDerivAt_px (hf.add hg) p.1 p.2).unique
    ((hasDerivAt_px hf p.1 p.2).add (hasDerivAt_px hg p.1 p.2))

private theorem py_add {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : ℝ × ℝ) : py (fun q => f q + g q) p = py f p + py g p :=
  (hasDerivAt_py (hf.add hg) p.1 p.2).unique
    ((hasDerivAt_py hf p.1 p.2).add (hasDerivAt_py hg p.1 p.2))

private theorem px_scale {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (p : ℝ × ℝ) :
    px (fun q => c * f q) p = c * px f p :=
  (hasDerivAt_px (contDiff_const.mul hf) p.1 p.2).unique
    ((hasDerivAt_px hf p.1 p.2).const_mul c)

private theorem py_scale {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (p : ℝ × ℝ) :
    py (fun q => c * f q) p = c * py f p :=
  (hasDerivAt_py (contDiff_const.mul hf) p.1 p.2).unique
    ((hasDerivAt_py hf p.1 p.2).const_mul c)

def denominator (p : ℝ × ℝ) : ℝ := 1 + p.1 ^ 2 + p.2 ^ 2

theorem denominator_pos (p : ℝ × ℝ) : 0 < denominator p := by
  unfold denominator
  positivity

private theorem denominator_smooth : ContDiff ℝ ∞ denominator := by
  unfold denominator
  fun_prop

private theorem denominator_x (x y : ℝ) :
    HasDerivAt (fun t => denominator (t, y)) (2 * x) x := by
  have h : HasDerivAt (fun t => denominator (t, y)) (2 * x ^ 1 * 1) x :=
    (((hasDerivAt_id x).pow 2).const_add 1).add_const (y ^ 2)
  simpa only [pow_one, mul_one] using h

private theorem denominator_y (x y : ℝ) :
    HasDerivAt (fun t => denominator (x, t)) (2 * y) y := by
  have h : HasDerivAt (fun t => denominator (x, t)) (2 * y ^ 1 * 1) y :=
    ((hasDerivAt_id y).pow 2).const_add (1 + x ^ 2)
  simpa only [pow_one, mul_one] using h

def inverseDenominator (p : ℝ × ℝ) : ℝ := (denominator p)⁻¹

private theorem inverseDenominator_smooth : ContDiff ℝ ∞ inverseDenominator :=
  denominator_smooth.inv (fun p => (denominator_pos p).ne')

private theorem inverseDenominator_px (p : ℝ × ℝ) :
    px inverseDenominator p = -(2 * p.1) / denominator p ^ 2 :=
  (hasDerivAt_px inverseDenominator_smooth p.1 p.2).unique
    ((denominator_x p.1 p.2).inv (denominator_pos p).ne')

private theorem inverseDenominator_py (p : ℝ × ℝ) :
    py inverseDenominator p = -(2 * p.2) / denominator p ^ 2 :=
  (hasDerivAt_py inverseDenominator_smooth p.1 p.2).unique
    ((denominator_y p.1 p.2).inv (denominator_pos p).ne')

private theorem inverseDenominator_pxx (p : ℝ × ℝ) :
    px (px inverseDenominator) p = -2 / denominator p ^ 2 + 8 * p.1 ^ 2 / denominator p ^ 3 := by
  have he : px inverseDenominator = fun q => -(2 * q.1) / denominator q ^ 2 :=
    funext inverseDenominator_px
  have hs : ContDiff ℝ ∞ (fun q : ℝ × ℝ => -(2 * q.1) / denominator q ^ 2) := by
    rw [← he]
    exact contDiff_px inverseDenominator_smooth
  have hd : HasDerivAt (fun t => -(2 * t) / denominator (t, p.2) ^ 2)
      (-2 / denominator p ^ 2 + 8 * p.1 ^ 2 / denominator p ^ 3) p.1 := by
    apply ((((hasDerivAt_id p.1).const_mul 2).neg).div
      ((denominator_x p.1 p.2).pow 2) (pow_ne_zero 2 (denominator_pos p).ne')).congr_deriv
    simp only [Pi.pow_apply, Pi.neg_apply, id_eq]
    field_simp [(denominator_pos p).ne']
    ring
  rw [he]
  exact (hasDerivAt_px hs p.1 p.2).unique hd

private theorem inverseDenominator_pyy (p : ℝ × ℝ) :
    py (py inverseDenominator) p = -2 / denominator p ^ 2 + 8 * p.2 ^ 2 / denominator p ^ 3 := by
  have he : py inverseDenominator = fun q => -(2 * q.2) / denominator q ^ 2 :=
    funext inverseDenominator_py
  have hs : ContDiff ℝ ∞ (fun q : ℝ × ℝ => -(2 * q.2) / denominator q ^ 2) := by
    rw [← he]
    exact contDiff_py inverseDenominator_smooth
  have hd : HasDerivAt (fun t => -(2 * t) / denominator (p.1, t) ^ 2)
      (-2 / denominator p ^ 2 + 8 * p.2 ^ 2 / denominator p ^ 3) p.2 := by
    apply ((((hasDerivAt_id p.2).const_mul 2).neg).div
      ((denominator_y p.1 p.2).pow 2) (pow_ne_zero 2 (denominator_pos p).ne')).congr_deriv
    simp only [Pi.pow_apply, Pi.neg_apply, id_eq]
    field_simp [(denominator_pos p).ne']
    ring
  rw [he]
  exact (hasDerivAt_py hs p.1 p.2).unique hd

private theorem inverseDenominator_pyx (p : ℝ × ℝ) :
    py (px inverseDenominator) p = 8 * p.1 * p.2 / denominator p ^ 3 := by
  have he : px inverseDenominator = fun q => -(2 * q.1) / denominator q ^ 2 :=
    funext inverseDenominator_px
  have hs : ContDiff ℝ ∞ (fun q : ℝ × ℝ => -(2 * q.1) / denominator q ^ 2) := by
    rw [← he]
    exact contDiff_px inverseDenominator_smooth
  have hd : HasDerivAt (fun t => -(2 * p.1) / denominator (p.1, t) ^ 2)
      (8 * p.1 * p.2 / denominator p ^ 3) p.2 := by
    apply ((hasDerivAt_const p.2 (-(2 * p.1))).div
      ((denominator_y p.1 p.2).pow 2) (pow_ne_zero 2 (denominator_pos p).ne')).congr_deriv
    simp only [Pi.pow_apply]
    field_simp [(denominator_pos p).ne']
    ring
  rw [he]
  exact (hasDerivAt_py hs p.1 p.2).unique hd

def support (U : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  1 + ε * (U p * inverseDenominator p)

theorem support_smooth {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (ε : ℝ) :
    ContDiff ℝ ∞ (support U ε) :=
  contDiff_const.add (contDiff_const.mul (hU.mul inverseDenominator_smooth))

private theorem support_px {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (ε : ℝ) (p : ℝ × ℝ) :
    px (support U ε) p = ε * (px U p * inverseDenominator p + U p * px inverseDenominator p) :=
  (hasDerivAt_px (support_smooth hU ε) p.1 p.2).unique
    ((((hasDerivAt_px hU p.1 p.2).mul
      (hasDerivAt_px inverseDenominator_smooth p.1 p.2)).const_mul ε).const_add 1)

private theorem support_py {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (ε : ℝ) (p : ℝ × ℝ) :
    py (support U ε) p = ε * (py U p * inverseDenominator p + U p * py inverseDenominator p) :=
  (hasDerivAt_py (support_smooth hU ε) p.1 p.2).unique
    ((((hasDerivAt_py hU p.1 p.2).mul
      (hasDerivAt_py inverseDenominator_smooth p.1 p.2)).const_mul ε).const_add 1)

private theorem support_pxx {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (ε : ℝ) (p : ℝ × ℝ) :
    px (px (support U ε)) p = ε * (px (px U) p * inverseDenominator p +
      2 * px U p * px inverseDenominator p + U p * px (px inverseDenominator) p) := by
  have he : px (support U ε) = fun q =>
      ε * (px U q * inverseDenominator q + U q * px inverseDenominator q) :=
    funext (support_px hU ε)
  have ha := (contDiff_px hU).mul inverseDenominator_smooth
  have hb := hU.mul (contDiff_px inverseDenominator_smooth)
  rw [he, px_scale (ha.add hb), px_add ha hb,
    px_mul (contDiff_px hU) inverseDenominator_smooth,
    px_mul hU (contDiff_px inverseDenominator_smooth)]
  ring

private theorem support_pyy {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (ε : ℝ) (p : ℝ × ℝ) :
    py (py (support U ε)) p = ε * (py (py U) p * inverseDenominator p +
      2 * py U p * py inverseDenominator p + U p * py (py inverseDenominator) p) := by
  have he : py (support U ε) = fun q =>
      ε * (py U q * inverseDenominator q + U q * py inverseDenominator q) :=
    funext (support_py hU ε)
  have ha := (contDiff_py hU).mul inverseDenominator_smooth
  have hb := hU.mul (contDiff_py inverseDenominator_smooth)
  rw [he, py_scale (ha.add hb), py_add ha hb,
    py_mul (contDiff_py hU) inverseDenominator_smooth,
    py_mul hU (contDiff_py inverseDenominator_smooth)]
  ring

private theorem support_pyx {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (ε : ℝ) (p : ℝ × ℝ) :
    py (px (support U ε)) p = ε * (py (px U) p * inverseDenominator p +
      px U p * py inverseDenominator p + py U p * px inverseDenominator p +
      U p * py (px inverseDenominator) p) := by
  have he : px (support U ε) = fun q =>
      ε * (px U q * inverseDenominator q + U q * px inverseDenominator q) :=
    funext (support_px hU ε)
  have ha := (contDiff_px hU).mul inverseDenominator_smooth
  have hb := hU.mul (contDiff_px inverseDenominator_smooth)
  rw [he, py_scale (ha.add hb), py_add ha hb,
    py_mul (contDiff_px hU) inverseDenominator_smooth,
    py_mul hU (contDiff_px inverseDenominator_smooth)]
  ring

/-- The first diagonal entry of the round-metric Hessian plus support function. -/
def radiusXX (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  denominator p ^ 2 / 4 *
    (px (px ρ) p + (2 * p.1 * px ρ p - 2 * p.2 * py ρ p) / denominator p) + ρ p

/-- The second diagonal entry of the round-metric Hessian plus support function. -/
def radiusYY (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  denominator p ^ 2 / 4 *
    (py (py ρ) p + (-2 * p.1 * px ρ p + 2 * p.2 * py ρ p) / denominator p) + ρ p

/-- The off-diagonal entry, with the conformal connection terms included. -/
def radiusXY (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  denominator p ^ 2 / 4 *
    (py (px ρ) p + (2 * p.2 * px ρ p + 2 * p.1 * py ρ p) / denominator p)

def scalarPart (U : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  1 + ε / 2 * (U p - p.1 * px U p - p.2 * py U p)

/-- Exact Bonnet decomposition, obtained from the actual derivatives of the support function. -/
theorem radius_decomposition {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (ε : ℝ) (p : ℝ × ℝ) :
    radiusXX (support U ε) p = scalarPart U ε p + ε * denominator p / 4 * px (px U) p ∧
    radiusYY (support U ε) p = scalarPart U ε p + ε * denominator p / 4 * py (py U) p ∧
    radiusXY (support U ε) p = ε * denominator p / 4 * py (px U) p := by
  have hd := (denominator_pos p).ne'
  constructor
  · unfold radiusXX
    rw [support_pxx hU, support_px hU, support_py hU,
      inverseDenominator_px, inverseDenominator_py, inverseDenominator_pxx]
    unfold support inverseDenominator scalarPart
    field_simp [hd]
    unfold denominator
    ring
  constructor
  · unfold radiusYY
    rw [support_pyy hU, support_px hU, support_py hU,
      inverseDenominator_px, inverseDenominator_py, inverseDenominator_pyy]
    unfold support inverseDenominator scalarPart
    field_simp [hd]
    unfold denominator
    ring
  · unfold radiusXY
    rw [support_pyx hU, support_px hU, support_py hU,
      inverseDenominator_px, inverseDenominator_py, inverseDenominator_pyx]
    unfold inverseDenominator
    field_simp [hd]
    ring

/-- The conformal radius matrix is scalar exactly where the Euclidean Hessian is scalar. -/
theorem radius_scalar_iff {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) {ε : ℝ} (hε : ε ≠ 0)
    (p : ℝ × ℝ) :
    (radiusXX (support U ε) p = radiusYY (support U ε) p ∧ radiusXY (support U ε) p = 0) ↔
      (px (px U) p = py (py U) p ∧ py (px U) p = 0) := by
  obtain ⟨hxx, hyy, hxy⟩ := radius_decomposition hU ε p
  rw [hxx, hyy, hxy]
  have hc : ε * denominator p / 4 ≠ 0 :=
    div_ne_zero (mul_ne_zero hε (denominator_pos p).ne') (by norm_num)
  constructor
  · rintro ⟨hd, hm⟩
    exact ⟨mul_left_cancel₀ hc (add_left_cancel hd), (mul_eq_zero.mp hm).resolve_left hc⟩
  · rintro ⟨hd, hm⟩
    rw [hd, hm, mul_zero]
    exact ⟨rfl, rfl⟩

#print axioms radius_decomposition
#print axioms radius_scalar_iff
end
end GaloisForLFunctions.HilbertMetric.Geometry.BonnetSupport
