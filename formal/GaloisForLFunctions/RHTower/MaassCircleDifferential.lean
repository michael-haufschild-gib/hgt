import GaloisForLFunctions.RHTower.MaassSmoothDifferentialOperators
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleChart

/-!
# The polar Laplacian of the original Maass source

Compose the proved hyperbolic circle chart with an arbitrary smooth function on
the upper half-plane. Actual first and second derivatives give the polar
Laplacian identity. Specialization uses the original Maass eigen-equation.
-/

open UpperHalfPlane Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.MaassCircle
open MaassSmooth
open _root_.RHTower.D4BMNativeCircle
noncomputable section

def circlePoint (d theta : ℝ) (z : ℍ) : ℍ :=
  ⟨⟨z.re + z.im * offset d theta, z.im * _root_.RHTower.D4BMNativeCircle.height d theta⟩,
    mul_pos z.im_pos (one_div_pos.mpr (denominator_pos d theta))⟩

@[simp] theorem circlePoint_im (d theta : ℝ) (z : ℍ) :
    (circlePoint d theta z).im = z.im * _root_.RHTower.D4BMNativeCircle.height d theta := rfl

theorem along_hasDerivAt (f : FunctionSpace) (p : ℝ → ℍ)
    (t a b : ℝ) (hp : HasDerivAt (fun r => (p r : ℂ)) ((a : ℂ) + (b : ℂ) * Complex.I) t) :
    HasDerivAt (fun r => f (p r))
      ((a : ℂ) * directional 1 f (p t) + (b : ℂ) * directional Complex.I f (p t)) t := by
  have hd := (MaassSmooth.differentiableAt f (p t)).hasFDerivAt.comp_hasDerivAt t hp
  have he : ((f : ℍ → ℂ) ∘ ofComplex) ∘ (fun r => (p r : ℂ)) =
      fun r => f (p r) := by funext r; simp only [Function.comp_apply, ofComplex_apply]
  rw [he] at hd
  apply hd.congr_deriv
  rw [map_add]
  have hmap (c : ℝ) (v : ℂ) :
      fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) (p t : ℂ) ((c : ℂ) * v) =
        (c : ℂ) * directional v f (p t) := by
    simpa only [Complex.real_smul, directional_apply] using
      (fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) (p t : ℂ)).map_smul c v
  rw [hmap]
  congr 1
  simpa only [mul_one] using hmap a 1

private theorem along_second (f : FunctionSpace) (p : ℝ → ℍ)
    (a b : ℝ → ℝ) (t a' b' : ℝ)
    (hp : ∀ r, HasDerivAt (fun s => (p s : ℂ)) ((a r : ℂ) + (b r : ℂ) * Complex.I) r)
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    deriv (deriv (fun r => f (p r))) t =
      (a t : ℂ)^2 * directional 1 (directional 1 f) (p t) +
      (a t : ℂ)*(b t : ℂ) * (directional Complex.I (directional 1 f) (p t) +
        directional 1 (directional Complex.I f) (p t)) +
      (b t : ℂ)^2 * directional Complex.I (directional Complex.I f) (p t) +
      (a' : ℂ) * directional 1 f (p t) + (b' : ℂ) * directional Complex.I f (p t) := by
  have he : deriv (fun r => f (p r)) = fun r =>
      (a r : ℂ) * directional 1 f (p r) + (b r : ℂ) * directional Complex.I f (p r) :=
    funext fun r => (along_hasDerivAt f p r (a r) (b r) (hp r)).deriv
  rw [he]
  have hca := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t ha
  have hcb := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hb
  have hx := along_hasDerivAt (directional 1 f) p t (a t) (b t) (hp t)
  have hy := along_hasDerivAt (directional Complex.I f) p t (a t) (b t) (hp t)
  have hh := (hca.mul hx).add (hcb.mul hy)
  simp only [Pi.add_def, Pi.mul_def, Function.comp_def, Complex.ofRealCLM_apply] at hh
  rw [hh.deriv]
  ring

theorem circlePoint_coe (d theta : ℝ) (z : ℍ) :
    (circlePoint d theta z : ℂ) =
      (z.re + z.im * offset d theta : ℝ) + (z.im * _root_.RHTower.D4BMNativeCircle.height d theta : ℝ) * Complex.I := by
  apply Complex.ext <;> simp [circlePoint]

theorem circle_radial (d theta : ℝ) (z : ℍ) :
    HasDerivAt (fun r => (circlePoint r theta z : ℂ))
      ((z.im * offsetRadial d theta : ℝ) + (z.im * heightRadial d theta : ℝ) * Complex.I) d := by
  have hx := ((offset_radial_derivatives d theta).1.const_mul z.im).const_add z.re
  have hy := (height_radial_derivatives d theta).1.const_mul z.im
  simpa only [circlePoint_coe, Pi.add_def, Function.comp_def, Complex.ofRealCLM_apply] using
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt d hx).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt d hy).mul_const Complex.I))

theorem circle_angular (d theta : ℝ) (z : ℍ) :
    HasDerivAt (fun t => (circlePoint d t z : ℂ))
      ((z.im * offsetAngular d theta : ℝ) + (z.im * heightAngular d theta : ℝ) * Complex.I) theta := by
  have hx := ((offset_angular_derivatives d theta).1.const_mul z.im).const_add z.re
  have hy := (height_angular_derivatives d theta).1.const_mul z.im
  simpa only [circlePoint_coe, Pi.add_def, Function.comp_def, Complex.ofRealCLM_apply] using
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt theta hx).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt theta hy).mul_const Complex.I))

theorem circle_polar (f : FunctionSpace) (d theta : ℝ) (z : ℍ) :
    (Real.sinh d : ℂ)^2 * deriv (deriv (fun r => f (circlePoint r theta z))) d +
      (Real.sinh d : ℂ)*(Real.cosh d : ℂ)*deriv (fun r => f (circlePoint r theta z)) d +
      deriv (deriv (fun t => f (circlePoint d t z))) theta =
      -(Real.sinh d : ℂ)^2 * positiveHyperbolicLaplacian (f : ℍ → ℂ) (circlePoint d theta z) := by
  rw [along_second f (fun r => circlePoint r theta z)
      (fun r => z.im * offsetRadial r theta) (fun r => z.im * heightRadial r theta) d
      (z.im * offsetRadialSecond d theta) (z.im * heightRadialSecond d theta)
      (fun r => circle_radial r theta z)
      ((offset_radial_derivatives d theta).2.const_mul z.im)
      ((height_radial_derivatives d theta).2.const_mul z.im),
    (along_hasDerivAt f (fun r => circlePoint r theta z) d
      (z.im * offsetRadial d theta) (z.im * heightRadial d theta)
      (circle_radial d theta z)).deriv,
    along_second f (fun t => circlePoint d t z)
      (fun t => z.im * offsetAngular d t) (fun t => z.im * heightAngular d t) theta
      (z.im * offsetAngularSecond d theta) (z.im * heightAngularSecond d theta)
      (fun t => circle_angular d t z)
      ((offset_angular_derivatives d theta).2.const_mul z.im)
      ((height_angular_derivatives d theta).2.const_mul z.im)]
  rw [← laplacian_apply]
  change _ = -(Real.sinh d : ℂ)^2 *
    (-(((circlePoint d theta z).im : ℂ) * (((circlePoint d theta z).im : ℂ) *
      (directional 1 (directional 1 f) (circlePoint d theta z) +
        directional Complex.I (directional Complex.I f) (circlePoint d theta z)))))
  rw [circlePoint_im]
  simp only [Complex.ofReal_mul]
  obtain ⟨hxx,hxy,hyy⟩ := polar_principal d theta
  obtain ⟨hx,hy⟩ := polar_connection d theta
  have hxxC : (Real.sinh d:ℂ)^2*(offsetRadial d theta:ℂ)^2+(offsetAngular d theta:ℂ)^2=
      (Real.sinh d:ℂ)^2*(_root_.RHTower.D4BMNativeCircle.height d theta:ℂ)^2 := by exact_mod_cast hxx
  have hxyC : (Real.sinh d:ℂ)^2*(offsetRadial d theta:ℂ)*(heightRadial d theta:ℂ)+
      (offsetAngular d theta:ℂ)*(heightAngular d theta:ℂ)=0 := by exact_mod_cast hxy
  have hyyC : (Real.sinh d:ℂ)^2*(heightRadial d theta:ℂ)^2+(heightAngular d theta:ℂ)^2=
      (Real.sinh d:ℂ)^2*(_root_.RHTower.D4BMNativeCircle.height d theta:ℂ)^2 := by exact_mod_cast hyy
  have hxC : (Real.sinh d:ℂ)^2*(offsetRadialSecond d theta:ℂ)+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(offsetRadial d theta:ℂ)+(offsetAngularSecond d theta:ℂ)=0 := by
    exact_mod_cast hx
  have hyC : (Real.sinh d:ℂ)^2*(heightRadialSecond d theta:ℂ)+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(heightRadial d theta:ℂ)+(heightAngularSecond d theta:ℂ)=0 := by
    exact_mod_cast hy
  linear_combination
    (z.im:ℂ)^2*directional 1 (directional 1 f) (circlePoint d theta z)*hxxC +
    (z.im:ℂ)^2*(directional Complex.I (directional 1 f) (circlePoint d theta z)+
      directional 1 (directional Complex.I f) (circlePoint d theta z))*hxyC +
    (z.im:ℂ)^2*directional Complex.I (directional Complex.I f) (circlePoint d theta z)*hyyC +
    (z.im:ℂ)*directional 1 f (circlePoint d theta z)*hxC +
    (z.im:ℂ)*directional Complex.I f (circlePoint d theta z)*hyC

theorem maass_circle_polar {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (d theta : ℝ) (z : ℍ) :
    (Real.sinh d : ℂ)^2 * deriv (deriv (fun r => f.1.1 (circlePoint r theta z))) d +
      (Real.sinh d : ℂ)*(Real.cosh d : ℂ)*deriv (fun r => f.1.1 (circlePoint r theta z)) d +
      deriv (deriv (fun t => f.1.1 (circlePoint d t z))) theta =
      -(Real.sinh d : ℂ)^2 * (lam : ℂ) * f.1.1 (circlePoint d theta z) := by
  have h := circle_polar (ofMaass f) d theta z
  change _ = -(Real.sinh d : ℂ)^2 * positiveHyperbolicLaplacian f.1.1 (circlePoint d theta z) at h
  rw [f.2.2.1.2] at h
  simpa only [ofMaass_apply, mul_assoc] using h

theorem circle_coordinates_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => offset p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => _root_.RHTower.D4BMNativeCircle.height p.1 p.2) := by
  have hoff : ContDiff ℝ ∞ (fun p : ℝ × ℝ => offset p.1 p.2) := by
    unfold offset
    apply ContDiff.div
    · fun_prop
    · unfold denominator; fun_prop
    · intro p; exact (denominator_pos p.1 p.2).ne'
  have hheight : ContDiff ℝ ∞ (fun p : ℝ × ℝ => _root_.RHTower.D4BMNativeCircle.height p.1 p.2) := by
    unfold _root_.RHTower.D4BMNativeCircle.height
    apply ContDiff.div
    · exact contDiff_const
    · unfold denominator; fun_prop
    · intro p; exact (denominator_pos p.1 p.2).ne'
  exact ⟨hoff, hheight⟩

theorem circle_source_smooth_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : FunctionSpace) (p : E → ℍ) (r theta : E → ℝ)
    (hp : ContDiff ℝ ∞ (fun x => (p x : ℂ)))
    (hr : ContDiff ℝ ∞ r) (htheta : ContDiff ℝ ∞ theta) :
    ContDiff ℝ ∞ (fun x => f (circlePoint (r x) (theta x) (p x))) := by
  have hx : ContDiff ℝ ∞ (fun x => (p x).re) := by
    simpa using! Complex.reCLM.contDiff.comp hp
  have hy : ContDiff ℝ ∞ (fun x => (p x).im) := by
    simpa using! Complex.imCLM.contDiff.comp hp
  have hoff := circle_coordinates_smooth.1.comp (hr.prodMk htheta)
  have hheight := circle_coordinates_smooth.2.comp (hr.prodMk htheta)
  have hc : ContDiff ℝ ∞ (fun x => (circlePoint (r x) (theta x) (p x) : ℂ)) := by
    simp only [circlePoint_coe]
    exact (Complex.ofRealCLM.contDiff.comp (hx.add (hy.mul hoff))).add
      ((Complex.ofRealCLM.contDiff.comp (hy.mul hheight)).mul contDiff_const)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have h := (regularAt f (circlePoint (r x) (theta x) (p x))).comp x hc.contDiffAt
  simpa only [Function.comp_def, ofComplex_apply] using h

theorem circle_source_smooth (f : FunctionSpace) (z : ℍ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (circlePoint p.1 p.2 z)) :=
  circle_source_smooth_family f (fun _ => z) Prod.fst Prod.snd
    contDiff_const contDiff_fst contDiff_snd

@[simp] theorem circlePoint_zero (theta : ℝ) (z : ℍ) : circlePoint 0 theta z = z := by
  apply UpperHalfPlane.ext
  apply Complex.ext <;> simp [circlePoint, offset, _root_.RHTower.D4BMNativeCircle.height, denominator]

theorem circlePoint_periodic (d theta : ℝ) (z : ℍ) :
    circlePoint d (theta + 2*Real.pi) z = circlePoint d theta z := by
  apply UpperHalfPlane.ext
  apply Complex.ext <;> simp [circlePoint, offset, _root_.RHTower.D4BMNativeCircle.height, denominator,
    Real.sin_add_two_pi, Real.cos_add_two_pi]

end
end GaloisForLFunctions.RHTower.MaassCircle
