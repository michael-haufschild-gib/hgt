import GaloisForLFunctions.RHTower.MaassCuspAutomorphicCorrespondence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Geometric interpolation of two hyperbolic quarter eigenfunctions

The positive fields `y^(1 / 2)` and `y^(1 / 2)/sqrt(x^(2 : ℕ)+y^(2 : ℕ))` have hyperbolic
Laplacian eigenvalue one quarter. Their geometric interpolation has the exact
additional potential `a*(1 - a)*y^(2 : ℕ)/(x^(2 : ℕ)+y^(2 : ℕ))`. At the symmetric interpolation this
potential is strictly positive, but every positive integer translation changes
the field. The differential identity therefore gives a local supersolution,
with an explicit obstruction to descending it by translation invariance.

All derivatives are those of the positive hyperbolic Laplacian used in the
Maass correspondence.
-/

open UpperHalfPlane Filter
open scoped Topology

namespace GaloisForLFunctions.RHTower.SelbergGeometricBlend
noncomputable section


/-- Squared Euclidean radius in the complex chart. -/
def radiusSq (w : ℂ) : ℝ := w.re ^ (2 : ℕ) + w.im ^ (2 : ℕ)

/-- Geometric interpolation of the positive half-densities at infinity and zero. -/
def realField (a : ℝ) (w : ℂ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * Real.log w.im - (a / 2) * Real.log (radiusSq w))

/-- The interpolated half-density as a field on the actual upper half-plane. -/
def field (a : ℝ) (z : ℍ) : ℂ := realField a (z : ℂ)

/-- Horizontal logarithmic derivative of the interpolated field. -/
def logX (a : ℝ) (w : ℂ) : ℝ := -a * w.re / radiusSq w
/-- Vertical logarithmic derivative of the interpolated field. -/
def logY (a : ℝ) (w : ℂ) : ℝ := 1 / (2 * w.im) - a * w.im / radiusSq w

/-- Real differential of the logarithm of the interpolated field. -/
def gradient (a : ℝ) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  logX a w • Complex.reCLM + logY a w • Complex.imCLM

private theorem radiusSq_pos {w : ℂ} (hw : 0 < w.im) : 0 < radiusSq w := by
  unfold radiusSq
  positivity

private theorem radiusSq_hasFDerivAt (w : ℂ) :
    HasFDerivAt radiusSq
      ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
  have hx : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have hy : HasFDerivAt (fun z : ℂ => z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  convert (hx.pow 2).add (hy.pow 2) using 1 <;> first | rfl | simp

private theorem realField_hasFDerivAt (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt (realField a) (realField a w • gradient a w) w := by
  have hd := (radiusSq_pos hw).ne'
  have hy : HasFDerivAt (fun z : ℂ => z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  have h := (((hy.log hw.ne').const_mul (1 / 2 : ℝ)).sub
    (((radiusSq_hasFDerivAt w).log hd).const_mul (a / 2))).exp
  convert h using 1 <;> try rfl
  ext u
  simp only [realField, gradient, logX, logY, add_apply,
    sub_apply, smul_apply, smul_eq_mul,
    Complex.reCLM_apply, Complex.imCLM_apply, Pi.sub_apply]
  field_simp
  ring

/-- The displayed logarithmic gradient is the actual differential of the field logarithm. -/
theorem log_realField_hasFDerivAt (a : ℝ) (z : ℍ) :
    HasFDerivAt (fun w : ℂ => Real.log (realField a w)) (gradient a (z : ℂ)) (z : ℂ) := by
  have hp : realField a (z : ℂ) ≠ 0 := (Real.exp_pos _).ne'
  have h := (realField_hasFDerivAt a z.im_pos).log hp
  convert h using 1 <;> try rfl
  simp [smul_smul, inv_mul_cancel₀ hp]

private theorem radiusInv_hasFDerivAt (w : ℂ) (hw : 0 < w.im) :
    HasFDerivAt (fun z => (radiusSq z)⁻¹)
      (-(radiusSq w ^ (2 : ℕ))⁻¹ •
        ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM)) w := by
  exact (hasDerivAt_inv (radiusSq_pos hw).ne').comp_hasFDerivAt w (radiusSq_hasFDerivAt w)

private theorem logX_hasFDerivAt (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt (logX a)
      ((-a / radiusSq w) • Complex.reCLM + (a * w.re / radiusSq w ^ (2 : ℕ)) •
        ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM)) w := by
  have hx : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have h := (hx.const_mul (-a)).fun_mul (radiusInv_hasFDerivAt w hw)
  convert h using 1 <;> try rfl
  all_goals
    ext u
    simp only [div_eq_mul_inv, add_apply, smul_apply, smul_eq_mul]
    ring

private theorem logY_hasFDerivAt (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt (logY a)
      ((-(1 / (2 * w.im ^ (2 : ℕ))) - a / radiusSq w) • Complex.imCLM +
        (a * w.im / radiusSq w ^ (2 : ℕ)) •
          ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM)) w := by
  have hy : HasFDerivAt (fun z : ℂ => z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  have hi := (hasDerivAt_inv hw.ne').comp_hasFDerivAt w hy
  have h := (hi.const_mul (1 / 2 : ℝ)).sub
    ((hy.const_mul a).fun_mul (radiusInv_hasFDerivAt w hw))
  convert h using 1 <;> try rfl
  · funext z
    simp only [logY, Function.comp_apply, Pi.sub_apply]
    ring
  · ext u
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
    field_simp [(radiusSq_pos hw).ne', hw.ne']
    ring

private theorem field_hasFDerivAt (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt (field a ∘ UpperHalfPlane.ofComplex)
      (Complex.ofRealCLM.comp (realField a w • gradient a w)) w := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp w (realField_hasFDerivAt a hw)
  have he : field a ∘ UpperHalfPlane.ofComplex =ᶠ[𝓝 w]
      (fun z : ℂ => (realField a z : ℂ)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with z hz
    simp [field, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact h.congr_of_eventuallyEq he

private theorem field_first_x (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    fderiv ℝ (field a ∘ UpperHalfPlane.ofComplex) w 1 =
      (realField a w * logX a w : ℝ) := by
  rw [(field_hasFDerivAt a hw).fderiv]
  simp [gradient]

private theorem field_first_y (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    fderiv ℝ (field a ∘ UpperHalfPlane.ofComplex) w Complex.I =
      (realField a w * logY a w : ℝ) := by
  rw [(field_hasFDerivAt a hw).fderiv]
  simp [gradient]

private theorem field_second_x (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    fderiv ℝ (fun z => fderiv ℝ (field a ∘ UpperHalfPlane.ofComplex) z 1) w 1 =
      (realField a w * (logX a w ^ (2 : ℕ) - a / radiusSq w +
        2 * a * w.re ^ (2 : ℕ) / radiusSq w ^ (2 : ℕ)) : ℝ) := by
  have he : (fun z => fderiv ℝ (field a ∘ UpperHalfPlane.ofComplex) z 1) =ᶠ[𝓝 w]
      (fun z : ℂ => ((realField a z * logX a z : ℝ) : ℂ)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with z hz
    exact field_first_x a hz
  have h := Complex.ofRealCLM.hasFDerivAt.comp w
    ((realField_hasFDerivAt a hw).fun_mul (logX_hasFDerivAt a hw))
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  rw [he.fderiv_eq, h.fderiv]
  simp [gradient]
  ring

private theorem field_second_y (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    fderiv ℝ (fun z => fderiv ℝ (field a ∘ UpperHalfPlane.ofComplex) z Complex.I)
      w Complex.I =
      (realField a w * (logY a w ^ (2 : ℕ) - 1 / (2 * w.im ^ (2 : ℕ)) - a / radiusSq w +
        2 * a * w.im ^ (2 : ℕ) / radiusSq w ^ (2 : ℕ)) : ℝ) := by
  have he : (fun z => fderiv ℝ (field a ∘ UpperHalfPlane.ofComplex) z Complex.I) =ᶠ[𝓝 w]
      (fun z : ℂ => ((realField a z * logY a z : ℝ) : ℂ)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with z hz
    exact field_first_y a hz
  have h := Complex.ofRealCLM.hasFDerivAt.comp w
    ((realField_hasFDerivAt a hw).fun_mul (logY_hasFDerivAt a hw))
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  rw [he.fderiv_eq, h.fderiv]
  simp [gradient]
  ring

/-- Exact hyperbolic equation, including the potential created by geometric interpolation. -/
theorem positiveHyperbolicLaplacian_field (a : ℝ) (z : ℍ) :
    positiveHyperbolicLaplacian (field a) z =
      (((1 / 4 : ℝ) + a * (1 - a) * z.im ^ (2 : ℕ) / (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) : ℝ) : ℂ) * field a z := by
  have hcoeff :
      -(z.im ^ (2 : ℕ)) *
        (logX a (z:ℂ) ^ (2 : ℕ) - a / radiusSq (z:ℂ) +
          2 * a * z.re ^ (2 : ℕ) / radiusSq (z:ℂ) ^ (2 : ℕ) +
         (logY a (z:ℂ) ^ (2 : ℕ) - 1 / (2 * z.im ^ (2 : ℕ)) - a / radiusSq (z:ℂ) +
          2 * a * z.im ^ (2 : ℕ) / radiusSq (z:ℂ) ^ (2 : ℕ))) =
        (1 / 4 : ℝ) + a * (1 - a) * z.im ^ (2 : ℕ) / (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) := by
    have hd := (radiusSq_pos z.im_pos).ne'
    simp only [logX, logY, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    field_simp [hd, z.im_ne_zero]
    simp only [radiusSq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  unfold positiveHyperbolicLaplacian
  rw [field_second_x a z.im_pos, field_second_y a z.im_pos]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  rw [← hcoeff]
  simp only [field]
  push_cast
  ring

/-- Every interpolated field has a strictly positive real value. -/
theorem field_re_pos (a : ℝ) (z : ℍ) : 0 < (field a z).re := by
  exact Real.exp_pos _

/-- The interpolation is real smooth on the upper half-plane. -/
theorem field_smooth (a : ℝ) : IsRealSmoothUpperHalfPlane (field a) := by
  intro w hw
  have hx : ContDiffAt ℝ 2 (fun z : ℂ => z.re) w := Complex.reCLM.contDiff.contDiffAt
  have hy : ContDiffAt ℝ 2 (fun z : ℂ => z.im) w := Complex.imCLM.contDiff.contDiffAt
  have hd : ContDiffAt ℝ 2 radiusSq w := (hx.pow 2).add (hy.pow 2)
  have hr : ContDiffAt ℝ 2 (realField a) w :=
    ((contDiffAt_const.mul (hy.log hw.ne')).sub
      (contDiffAt_const.mul (hd.log (radiusSq_pos hw).ne'))).exp
  have hc : ContDiffAt ℝ 2 (fun z : ℂ => (realField a z : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w hr
  have he : field a ∘ UpperHalfPlane.ofComplex =ᶠ[𝓝 w]
      (fun z : ℂ => (realField a z : ℂ)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with z hz
    simp [field, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact (hc.congr_of_eventuallyEq he).contDiffWithinAt

/-- The symmetric interpolation has the explicit additional potential `y^(2 : ℕ)/(4*(x^(2 : ℕ)+y^(2 : ℕ)))`. -/
theorem half_laplacian (z : ℍ) :
    (positiveHyperbolicLaplacian (field (1 / 2)) z).re =
      ((1 / 4 : ℝ) + z.im ^ (2 : ℕ) / (4 * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)))) * (field (1 / 2) z).re := by
  rw [positiveHyperbolicLaplacian_field]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hd : z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) ≠ 0 := (radiusSq_pos z.im_pos).ne'
  field_simp [hd]
  ring

/-- The symmetric interpolant is a strict local supersolution at one quarter. -/
theorem half_strict_quarter (z : ℍ) :
    (1 / 4 : ℝ) * (field (1 / 2) z).re <
      (positiveHyperbolicLaplacian (field (1 / 2)) z).re := by
  rw [half_laplacian]
  have hgain : 0 < z.im ^ (2 : ℕ) / (4 * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ))) := by
    have hy := z.im_pos
    positivity
  nlinarith [mul_pos hgain (field_re_pos (1 / 2) z)]

/-- The imaginary unit in the upper half-plane. -/
def basePoint : ℍ := ⟨Complex.I, by simp⟩

/-- Translation of the imaginary unit by a positive integer. -/
def translatedBasePoint (n : ℕ) : ℍ :=
  ⟨((n + 1 : ℕ) : ℂ) + Complex.I, by simp⟩

/-- Every member of the family has value one at the imaginary unit. -/
theorem field_basePoint (a : ℝ) : field a basePoint = 1 := by
  simp [field, realField, basePoint, radiusSq]

/-- Every positive integer translation strictly decreases the symmetric field at the base point. -/
theorem half_translatedBasePoint_lt (n : ℕ) :
    (field (1 / 2) (translatedBasePoint n)).re < (field (1 / 2) basePoint).re := by
  rw [field_basePoint]
  simp only [field, realField, translatedBasePoint, radiusSq, Complex.ofReal_re,
    Complex.add_re, Complex.add_im,
    Complex.natCast_re, Complex.natCast_im, Complex.I_re, Complex.I_im,
    add_zero, zero_add, one_pow, Real.log_one, mul_zero, zero_sub, Complex.one_re]
  apply Real.exp_lt_one_iff.mpr
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog : 0 < Real.log (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) + 1) :=
    Real.log_pos (by nlinarith [sq_pos_of_pos hn])
  nlinarith

/-- The local supersolution fails every positive integer translation test. -/
theorem half_translatedBasePoint_ne (n : ℕ) :
    field (1 / 2) (translatedBasePoint n) ≠ field (1 / 2) basePoint := by
  intro h
  exact (ne_of_lt (half_translatedBasePoint_lt n)) (congrArg Complex.re h)

/-- The symmetric field is exactly the positive geometric mean of the two endpoint fields. -/
theorem half_sq_eq_endpoints (z : ℍ) :
    field (1 / 2) z ^ (2 : ℕ) = field 0 z * field 1 z := by
  have h : realField (1 / 2) (z:ℂ) ^ (2 : ℕ) = realField 0 (z:ℂ) * realField 1 (z:ℂ) := by
    unfold realField
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold field
  exact_mod_cast h

/-- The boundary-infinity endpoint has hyperbolic eigenvalue one quarter. -/
theorem endpoint_zero_equation (z : ℍ) :
    positiveHyperbolicLaplacian (field 0) z = (1 / 4 : ℂ) * field 0 z := by
  simpa using positiveHyperbolicLaplacian_field 0 z

/-- The boundary-zero endpoint has hyperbolic eigenvalue one quarter. -/
theorem endpoint_one_equation (z : ℍ) :
    positiveHyperbolicLaplacian (field 1) z = (1 / 4 : ℂ) * field 1 z := by
  simpa using positiveHyperbolicLaplacian_field 1 z

/-- The infinity endpoint satisfies the actual smooth Maass eigenfunction predicate. -/
theorem endpoint_zero_eigenfunction : IsMaassEigenfunction (1 / 4) (field 0) := by
  refine ⟨field_smooth 0, fun z => ?_⟩
  simpa using endpoint_zero_equation z

/-- The zero endpoint satisfies the actual smooth Maass eigenfunction predicate. -/
theorem endpoint_one_eigenfunction : IsMaassEigenfunction (1 / 4) (field 1) := by
  refine ⟨field_smooth 1, fun z => ?_⟩
  simpa using endpoint_one_equation z

end
end GaloisForLFunctions.RHTower.SelbergGeometricBlend
