import GaloisForLFunctions.HilbertMetric.Geometry.StereographicFrame
import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzRadius

/-!
# Actual support-surface derivatives

The parametrization is the support function times the sphere normal plus
its round gradient. Differentiation gives the radius matrix in the actual
stereographic tangent frame, so positivity implies regularity.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.BonnetSurface
open GaloisForLFunctions.HTGeometry.GaussBonnet
open BonnetSupport StereographicFrame SchwartzRadius
noncomputable section

/-- The support-function parametrization in the Euclidean ambient space. -/
def surface (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Space :=
  ρ p • normal p + (denominator p ^ 2 / 4) •
    (px ρ p • tangentX p + py ρ p • tangentY p)

theorem surface_smooth {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (surface ρ) := by
  have hd : ContDiff ℝ ∞ (fun p => denominator p ^ 2 / 4) := by
    unfold denominator
    fun_prop
  exact (hρ.smul normal_smooth).add
    (hd.smul (((contDiff_px hρ).smul tangentX_smooth).add ((contDiff_py hρ).smul tangentY_smooth)))

private theorem px_py_comm {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (p : ℝ × ℝ) :
    px (py ρ) p = py (px ρ) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ρ) p :=
    (hρ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p
  unfold px py
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  have hs : fderiv ℝ (fderiv ℝ ρ) p (1, 0) (0, 1) =
      fderiv ℝ (fderiv ℝ ρ) p (0, 1) (1, 0) :=
    hρ.contDiffAt.isSymmSndFDerivAt
      (by norm_num; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) (1, 0) (0, 1)
  simpa using hs

/-- The radius matrix gives the actual derivative of the support surface along every plane curve. -/
theorem surface_path {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {u v : ℝ → ℝ} {u' v' t : ℝ} (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => surface ρ (u s, v s))
      (u' • (radiusXX ρ (u t, v t) • tangentX (u t, v t) +
        radiusXY ρ (u t, v t) • tangentY (u t, v t)) +
       v' • (radiusXY ρ (u t, v t) • tangentX (u t, v t) +
        radiusYY ρ (u t, v t) • tangentY (u t, v t))) t := by
  have hr := hasDerivAt_comp_curve hρ hu hv
  have hx := hasDerivAt_comp_curve (contDiff_px hρ) hu hv
  have hy := hasDerivAt_comp_curve (contDiff_py hρ) hu hv
  have hd := ((denominator_path hu hv).pow 2).div_const 4
  have hn := normal_path hu hv
  have hnx := tangentX_path hu hv
  have hny := tangentY_path hu hv
  have h := (hr.smul hn).add (hd.smul ((hx.smul hnx).add (hy.smul hny)))
  change HasDerivAt (fun s => surface ρ (u s, v s)) _ t at h
  apply h.congr_deriv
  ext i
  simp [PiLp.add_apply, PiLp.smul_apply]
  rw [px_py_comm hρ]
  unfold radiusXX radiusXY radiusYY
  field_simp [(denominator_pos (u t, v t)).ne']
  ring

/-- Coordinate tangent vectors are actual derivatives, not formal coefficient fields. -/
theorem surface_partials {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (p : ℝ × ℝ) :
    deriv (fun t => surface ρ (t, p.2)) p.1 =
      radiusXX ρ p • tangentX p + radiusXY ρ p • tangentY p ∧
    deriv (fun t => surface ρ (p.1, t)) p.2 =
      radiusXY ρ p • tangentX p + radiusYY ρ p • tangentY p := by
  constructor
  · simpa only [one_smul, zero_smul, add_zero, id_eq, Prod.mk.eta] using
      (surface_path hρ (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)).deriv
  · simpa only [one_smul, zero_smul, zero_add, id_eq, Prod.mk.eta] using
      (surface_path hρ (hasDerivAt_const p.2 p.1) (hasDerivAt_id p.2)).deriv

/-- The stereographic sphere normal is perpendicular to both actual surface tangents. -/
theorem surface_normal {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (p : ℝ × ℝ) :
    inner ℝ (normal p) (deriv (fun t => surface ρ (t, p.2)) p.1) = 0 ∧
    inner ℝ (normal p) (deriv (fun t => surface ρ (p.1, t)) p.2) = 0 := by
  obtain ⟨hx, hy⟩ := surface_partials hρ p
  obtain ⟨_, hnx, hny⟩ := normal_metric p
  rw [hx, hy]
  simp only [inner_add_right, inner_smul_right, hnx, hny, mul_zero, add_zero, and_self]

/-- Every Schwartz perturbation at its explicit positive scale gives a regular smooth surface. -/
theorem schwartz_surface_regular (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) (a b : ℝ)
    (hzero : a • deriv (fun t => surface (support f (positiveScale f)) (t, p.2)) p.1 +
      b • deriv (fun t => surface (support f (positiveScale f)) (p.1, t)) p.2 = 0) :
    a = 0 ∧ b = 0 := by
  let ρ := support f (positiveScale f)
  have hρ : ContDiff ℝ ∞ ρ := support_smooth (f.smooth ⊤) _
  obtain ⟨hx, hy⟩ := surface_partials hρ p
  change a • deriv (fun t => surface ρ (t, p.2)) p.1 +
    b • deriv (fun t => surface ρ (p.1, t)) p.2 = 0 at hzero
  rw [hx, hy] at hzero
  obtain ⟨hxx, hyy, hxy⟩ := tangent_metric p
  have hyx : inner ℝ (tangentY p) (tangentX p) = 0 := by rw [real_inner_comm, hxy]
  have hix := congrArg (fun w => inner ℝ w (tangentX p)) hzero
  have hiy := congrArg (fun w => inner ℝ w (tangentY p)) hzero
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    hxx, hyy, hxy, hyx, inner_zero_left, mul_zero, add_zero, zero_add] at hix hiy
  have hc : (2 / denominator p) ^ 2 ≠ 0 := pow_ne_zero 2
    (div_ne_zero (by norm_num) (denominator_pos p).ne')
  have he₁ : a * radiusXX ρ p + b * radiusXY ρ p = 0 := by
    apply (mul_eq_zero.mp (show (a * radiusXX ρ p + b * radiusXY ρ p) *
      (2 / denominator p) ^ 2 = 0 by nlinarith only [hix])).resolve_right hc
  have he₂ : a * radiusXY ρ p + b * radiusYY ρ p = 0 := by
    apply (mul_eq_zero.mp (show (a * radiusXY ρ p + b * radiusYY ρ p) *
      (2 / denominator p) ^ 2 = 0 by nlinarith only [hiy])).resolve_right hc
  have he : radiusXX ρ p * a ^ 2 + 2 * radiusXY ρ p * a * b +
      radiusYY ρ p * b ^ 2 = 0 := by
    nlinarith only [congrArg (fun t => a * t) he₁, congrArg (fun t => b * t) he₂]
  have hp := radius_uniform_positive f p a b
  change (a ^ 2 + b ^ 2) / 2 ≤ radiusXX ρ p * a ^ 2 +
    2 * radiusXY ρ p * a * b + radiusYY ρ p * b ^ 2 at hp
  rw [he] at hp
  exact ⟨by nlinarith only [hp, sq_nonneg b], by nlinarith only [hp, sq_nonneg a]⟩

/-- The differential has the two actual coordinate derivatives as its columns. -/
theorem surface_fderiv_apply {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (p v : ℝ × ℝ) :
    fderiv ℝ (surface ρ) p v =
      v.1 • deriv (fun t => surface ρ (t, p.2)) p.1 +
      v.2 • deriv (fun t => surface ρ (p.1, t)) p.2 := by
  have hd := ((surface_smooth hρ).differentiable (by simp) p).hasFDerivAt
  have hx := (hd.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv
  have hy := (hd.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
  change deriv (fun t => surface ρ (t, p.2)) p.1 =
    fderiv ℝ (surface ρ) p (1, 0) at hx
  change deriv (fun t => surface ρ (p.1, t)) p.2 =
    fderiv ℝ (surface ρ) p (0, 1) at hy
  rw [hx, hy]
  have he : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by simp
  conv_lhs => rw [he, map_add, map_smul, map_smul]

/-- The concrete Schwartz support surface is an immersion in the usual Fréchet sense. -/
theorem schwartz_surface_fderiv_injective (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (surface (support f (positiveScale f))) p) := by
  intro v w h
  have hz : fderiv ℝ (surface (support f (positiveScale f))) p (v - w) = 0 := by
    rw [map_sub, h, sub_self]
  rw [surface_fderiv_apply (support_smooth (f.smooth ⊤) _)] at hz
  obtain ⟨hx, hy⟩ := schwartz_surface_regular f p (v - w).1 (v - w).2 hz
  exact Prod.ext (sub_eq_zero.mp hx) (sub_eq_zero.mp hy)

/-- The explicit displacement from the round sphere. -/
def correction (U : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Space :=
  !₂[px U p / 2, py U p / 2, 0] +
    ((U p - p.1 * px U p - p.2 * py U p) / denominator p) • !₂[p.1, p.2, -1]

private theorem support_first {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U)
    (ε : ℝ) (p : ℝ × ℝ) :
    px (support U ε) p = ε * (px U p * denominator p - U p * (2 * p.1)) / denominator p ^ 2 ∧
    py (support U ε) p = ε * (py U p * denominator p - U p * (2 * p.2)) / denominator p ^ 2 := by
  have hx := (((hasDerivAt_px hU p.1 p.2).div
    (denominator_path (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2))
      (denominator_pos p).ne').const_mul ε).const_add 1
  have hy := (((hasDerivAt_py hU p.1 p.2).div
    (denominator_path (hasDerivAt_const p.2 p.1) (hasDerivAt_id p.2))
      (denominator_pos p).ne').const_mul ε).const_add 1
  constructor
  · have he := (hasDerivAt_px (support_smooth hU ε) p.1 p.2).unique hx
    simpa only [id_eq, Prod.mk.eta, mul_one, mul_zero, add_zero, mul_div_assoc] using he
  · have he := (hasDerivAt_py (support_smooth hU ε) p.1 p.2).unique hy
    simpa only [id_eq, Prod.mk.eta, mul_one, mul_zero, zero_add, mul_div_assoc] using he

/-- Exact displacement formula, involving only first derivatives and a harmless rational weight. -/
theorem surface_eq_normal_add {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U)
    (ε : ℝ) (p : ℝ × ℝ) :
    surface (support U ε) p = normal p + ε • correction U p := by
  obtain ⟨hx, hy⟩ := support_first hU ε p
  unfold surface
  rw [hx, hy]
  ext i
  fin_cases i <;>
    simp [normal_formula, tangentX, tangentY, correction, support, inverseDenominator,
      PiLp.add_apply, PiLp.smul_apply] <;>
    field_simp [(denominator_pos p).ne'] <;> unfold denominator <;> ring

/-- A scalar Gauss differential is equivalent to a nonzero scalar radius matrix.
Both sides use the actual derivatives of the parametrization and its unit normal. -/
theorem gauss_derivative_scalar_iff {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (p : ℝ × ℝ) :
    (∃ κ : ℝ,
      deriv (fun t => normal (t, p.2)) p.1 =
        κ • deriv (fun t => surface ρ (t, p.2)) p.1 ∧
      deriv (fun t => normal (p.1, t)) p.2 =
        κ • deriv (fun t => surface ρ (p.1, t)) p.2) ↔
      radiusXX ρ p = radiusYY ρ p ∧ radiusXY ρ p = 0 ∧ radiusXX ρ p ≠ 0 := by
  obtain ⟨hnx, hny⟩ := normal_partials p
  obtain ⟨hsx, hsy⟩ := surface_partials hρ p
  rw [hnx, hny, hsx, hsy]
  obtain ⟨hxx, hyy, hxy⟩ := tangent_metric p
  have hyx : inner ℝ (tangentY p) (tangentX p) = 0 := by rw [real_inner_comm, hxy]
  have hc : (2 / denominator p) ^ 2 ≠ 0 := pow_ne_zero 2
    (div_ne_zero (by norm_num) (denominator_pos p).ne')
  constructor
  · rintro ⟨κ, hx, hy⟩
    have hix := congrArg (fun w => inner ℝ w (tangentX p)) hx
    have hiy := congrArg (fun w => inner ℝ w (tangentY p)) hy
    have him := congrArg (fun w => inner ℝ w (tangentY p)) hx
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
      hxx, hyy, hxy, hyx, mul_zero, add_zero, zero_add] at hix hiy him
    have he₁ : 1 = κ * radiusXX ρ p := by
      apply mul_right_cancel₀ hc
      nlinarith only [hix]
    have he₂ : 1 = κ * radiusYY ρ p := by
      apply mul_right_cancel₀ hc
      nlinarith only [hiy]
    have hκ : κ ≠ 0 := by intro h; rw [h, zero_mul] at he₁; norm_num at he₁
    have hm : radiusXY ρ p = 0 := by
      have hz : κ * radiusXY ρ p * (2 / denominator p) ^ 2 = 0 := by
        nlinarith only [him]
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hc)).resolve_left hκ
    have hd : radiusXX ρ p ≠ 0 := by intro h; rw [h, mul_zero] at he₁; norm_num at he₁
    exact ⟨mul_left_cancel₀ hκ (he₁.symm.trans he₂), hm, hd⟩
  · rintro ⟨hd, hm, hn⟩
    refine ⟨(radiusXX ρ p)⁻¹, ?_, ?_⟩
    · rw [hm, zero_smul, add_zero, smul_smul, inv_mul_cancel₀ hn, one_smul]
    · rw [← hd, hm, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ hn, one_smul]

#print axioms surface_fderiv_apply
#print axioms schwartz_surface_fderiv_injective
#print axioms surface_path
#print axioms surface_normal
#print axioms schwartz_surface_regular
#print axioms gauss_derivative_scalar_iff
#print axioms surface_eq_normal_add
end
end GaloisForLFunctions.HilbertMetric.Geometry.BonnetSurface
