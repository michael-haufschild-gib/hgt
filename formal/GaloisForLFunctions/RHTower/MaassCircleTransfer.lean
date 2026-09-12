import GaloisForLFunctions.RHTower.MaassCircleDifferential

/-!
# Transfer of base-point Euler derivatives to hyperbolic circle coordinates

Horizontal translation at speed y and vertical scaling generate y*d_x and
 y*d_y at the base point. On the actual circle pullback these derivatives are
radial/angular vector fields with coefficients independent of that base point.
The identities follow from the original circle derivatives, without estimates
on derivatives of the source.
-/

open UpperHalfPlane Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.MaassCircle
open MaassSmooth _root_.RHTower.D4BMNativeCircle
noncomputable section

theorem horizontal_transfer_coefficients {r : ℝ} (hr : 0 < r) (theta : ℝ) :
    Real.sin theta * offsetRadial r theta +
      (Real.cosh r / Real.sinh r * Real.cos theta - 1) * offsetAngular r theta = 1 ∧
    Real.sin theta * heightRadial r theta +
      (Real.cosh r / Real.sinh r * Real.cos theta - 1) * heightAngular r theta = 0 := by
  have hs := (Real.sinh_pos_iff.mpr hr).ne'
  have hn := (denominator_pos r theta).ne'
  have hb : Real.cosh r / Real.sinh r * Real.cos theta - 1 =
      -radialNumerator r theta / Real.sinh r := by
    unfold radialNumerator
    field_simp
    ring
  have hid : Real.sin theta ^ 2 + radialNumerator r theta ^ 2 = denominator r theta ^ 2 := by
    unfold radialNumerator denominator
    linear_combination (Real.cos theta ^ 2 - 1) * Real.cosh_sq_sub_sinh_sq r +
      Real.sin_sq_add_cos_sq theta
  rw [hb]
  constructor
  · calc
      _ = (Real.sin theta ^ 2 + radialNumerator r theta ^ 2) / denominator r theta ^ 2 := by
        unfold offsetRadial offsetAngular
        field_simp
      _ = 1 := by rw [hid]; exact div_self (pow_ne_zero 2 hn)
  · unfold heightRadial heightAngular
    field_simp
    ring

theorem vertical_transfer_coefficients {r : ℝ} (hr : 0 < r) (theta : ℝ) :
    Real.cos theta * offsetRadial r theta -
      (Real.cosh r / Real.sinh r * Real.sin theta) * offsetAngular r theta = offset r theta ∧
    Real.cos theta * heightRadial r theta -
      (Real.cosh r / Real.sinh r * Real.sin theta) * heightAngular r theta =
      _root_.RHTower.D4BMNativeCircle.height r theta := by
  have hs := (Real.sinh_pos_iff.mpr hr).ne'
  have hn := (denominator_pos r theta).ne'
  have hx : Real.cos theta + Real.cosh r * radialNumerator r theta =
      Real.sinh r * denominator r theta := by
    unfold radialNumerator denominator
    linear_combination -Real.cos theta * Real.cosh_sq_sub_sinh_sq r
  have hy : -Real.cos theta * radialNumerator r theta + Real.cosh r * Real.sin theta ^ 2 =
      denominator r theta := by
    unfold radialNumerator denominator
    linear_combination Real.cosh r * Real.sin_sq_add_cos_sq theta
  constructor
  · calc
      _ = Real.sin theta * (Real.cos theta + Real.cosh r * radialNumerator r theta) /
          denominator r theta ^ 2 := by
        unfold offsetRadial offsetAngular
        field_simp
        ring
      _ = offset r theta := by rw [hx]; unfold offset; field_simp
  · calc
      _ = (-Real.cos theta * radialNumerator r theta + Real.cosh r * Real.sin theta ^ 2) /
          denominator r theta ^ 2 := by
        unfold heightRadial heightAngular
        field_simp
        ring
      _ = _root_.RHTower.D4BMNativeCircle.height r theta := by
        rw [hy]; unfold _root_.RHTower.D4BMNativeCircle.height; field_simp

def horizontalFlow (t : ℝ) (z : ℍ) : ℍ := ⟨⟨z.re + t*z.im,z.im⟩,z.im_pos⟩
def verticalFlow (t : ℝ) (z : ℍ) : ℍ :=
  ⟨⟨z.re,Real.exp t*z.im⟩,mul_pos (Real.exp_pos t) z.im_pos⟩

@[simp] theorem horizontalFlow_zero (z : ℍ) : horizontalFlow 0 z = z := by
  apply UpperHalfPlane.ext; apply Complex.ext <;> simp [horizontalFlow]
@[simp] theorem verticalFlow_zero (z : ℍ) : verticalFlow 0 z = z := by
  apply UpperHalfPlane.ext; apply Complex.ext <;> simp [verticalFlow]

theorem circle_base_hasDerivAt (r theta : ℝ) (p : ℝ → ℍ) (t a b : ℝ)
    (hp : HasDerivAt (fun s => (p s : ℂ)) ((a : ℂ)+(b : ℂ)*Complex.I) t) :
    HasDerivAt (fun s => (circlePoint r theta (p s) : ℂ))
      ((a+b*offset r theta : ℝ)+(b*_root_.RHTower.D4BMNativeCircle.height r theta : ℝ)*Complex.I) t := by
  have hx : HasDerivAt (fun s => (p s).re) a t := by
    simpa using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
  have hy : HasDerivAt (fun s => (p s).im) b t := by
    simpa using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hp
  simpa only [circlePoint_coe, Pi.add_def, Function.comp_def, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hx.add (hy.mul_const _))).add
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hy.mul_const _)).mul_const Complex.I)

theorem horizontalFlow_hasDerivAt (z : ℍ) :
    HasDerivAt (fun t => (horizontalFlow t z : ℂ)) ((z.im : ℂ)+(0 : ℂ)*Complex.I) 0 := by
  have he : (fun t => (horizontalFlow t z : ℂ)) =
      fun t : ℝ => (z : ℂ)+(t : ℂ)*(z.im : ℂ) := by
    funext t
    apply Complex.ext <;> simp [horizontalFlow]
  rw [he]
  simpa using ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id 0)).mul_const
    (z.im : ℂ)).const_add (z : ℂ)

theorem verticalFlow_hasDerivAt (z : ℍ) :
    HasDerivAt (fun t => (verticalFlow t z : ℂ)) ((0 : ℂ)+(z.im : ℂ)*Complex.I) 0 := by
  have he : (fun t => (verticalFlow t z : ℂ)) =
      fun t : ℝ => (z.re : ℂ)+(Real.exp t*z.im : ℝ)*Complex.I := by
    funext t
    apply Complex.ext <;>
      simp only [verticalFlow, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, add_zero, sub_zero, zero_add, mul_one]
  rw [he]
  simpa using ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    ((Real.hasDerivAt_exp 0).mul_const z.im)).mul_const Complex.I).const_add (z.re : ℂ)

theorem horizontal_source_deriv (f : FunctionSpace) (z : ℍ) :
    deriv (fun t => f (horizontalFlow t z)) 0 =
      (z.im : ℂ)*directional 1 f z := by
  simpa only [horizontalFlow_zero, Complex.ofReal_zero, zero_mul, add_zero] using
    (along_hasDerivAt f (fun t => horizontalFlow t z) 0 z.im 0 (horizontalFlow_hasDerivAt z)).deriv

theorem vertical_source_deriv (f : FunctionSpace) (z : ℍ) :
    deriv (fun t => f (verticalFlow t z)) 0 =
      (z.im : ℂ)*directional Complex.I f z := by
  simpa only [verticalFlow_zero, Complex.ofReal_zero, zero_mul, zero_add] using
    (along_hasDerivAt f (fun t => verticalFlow t z) 0 0 z.im (verticalFlow_hasDerivAt z)).deriv

theorem horizontal_circle_transfer (f : FunctionSpace) (z : ℍ) {r : ℝ}
    (hr : 0 < r) (theta : ℝ) :
    deriv (fun t => f (circlePoint r theta (horizontalFlow t z))) 0 =
      (Real.sin theta : ℂ)*deriv (fun t => f (circlePoint t theta z)) r +
      (Real.cosh r / Real.sinh r * Real.cos theta - 1 : ℝ)*
        deriv (fun t => f (circlePoint r t z)) theta := by
  rw [(along_hasDerivAt f (fun t => circlePoint r theta (horizontalFlow t z)) 0
      (z.im+0*offset r theta) (0*_root_.RHTower.D4BMNativeCircle.height r theta)
      (circle_base_hasDerivAt r theta _ 0 z.im 0 (horizontalFlow_hasDerivAt z))).deriv,
    (along_hasDerivAt f _ r _ _ (circle_radial r theta z)).deriv,
    (along_hasDerivAt f _ theta _ _ (circle_angular r theta z)).deriv]
  simp only [zero_mul, add_zero, Complex.ofReal_zero, horizontalFlow_zero, Complex.ofReal_mul]
  obtain ⟨hx,hy⟩ := horizontal_transfer_coefficients hr theta
  have hxC : (Real.sin theta : ℂ)*(offsetRadial r theta : ℂ)+
      (Real.cosh r / Real.sinh r * Real.cos theta - 1 : ℝ)*(offsetAngular r theta : ℂ)=1 := by
    exact_mod_cast hx
  have hyC : (Real.sin theta : ℂ)*(heightRadial r theta : ℂ)+
      (Real.cosh r / Real.sinh r * Real.cos theta - 1 : ℝ)*(heightAngular r theta : ℂ)=0 := by
    exact_mod_cast hy
  linear_combination -(z.im : ℂ)*directional 1 f (circlePoint r theta z)*hxC -
    (z.im : ℂ)*directional Complex.I f (circlePoint r theta z)*hyC

theorem vertical_circle_transfer (f : FunctionSpace) (z : ℍ) {r : ℝ}
    (hr : 0 < r) (theta : ℝ) :
    deriv (fun t => f (circlePoint r theta (verticalFlow t z))) 0 =
      (Real.cos theta : ℂ)*deriv (fun t => f (circlePoint t theta z)) r -
      (Real.cosh r / Real.sinh r * Real.sin theta : ℝ)*
        deriv (fun t => f (circlePoint r t z)) theta := by
  rw [(along_hasDerivAt f (fun t => circlePoint r theta (verticalFlow t z)) 0
      (0+z.im*offset r theta) (z.im*_root_.RHTower.D4BMNativeCircle.height r theta)
      (circle_base_hasDerivAt r theta _ 0 0 z.im (verticalFlow_hasDerivAt z))).deriv,
    (along_hasDerivAt f _ r _ _ (circle_radial r theta z)).deriv,
    (along_hasDerivAt f _ theta _ _ (circle_angular r theta z)).deriv]
  simp only [zero_add, verticalFlow_zero, Complex.ofReal_mul]
  obtain ⟨hx,hy⟩ := vertical_transfer_coefficients hr theta
  have hxC : (Real.cos theta : ℂ)*(offsetRadial r theta : ℂ)-
      (Real.cosh r / Real.sinh r * Real.sin theta : ℝ)*(offsetAngular r theta : ℂ)=offset r theta := by
    exact_mod_cast hx
  have hyC : (Real.cos theta : ℂ)*(heightRadial r theta : ℂ)-
      (Real.cosh r / Real.sinh r * Real.sin theta : ℝ)*(heightAngular r theta : ℂ)=
      _root_.RHTower.D4BMNativeCircle.height r theta := by
    exact_mod_cast hy
  simp only [Complex.ofReal_mul] at hxC hyC
  linear_combination -(z.im : ℂ)*directional 1 f (circlePoint r theta z)*hxC -
    (z.im : ℂ)*directional Complex.I f (circlePoint r theta z)*hyC

end
end GaloisForLFunctions.RHTower.MaassCircle
