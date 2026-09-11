import GaloisForLFunctions.RHTower.MaassCuspSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Smooth Maass differential operators

Directional derivatives and multiplication by height act on the original smooth
upper-half-plane functions. Their product and commutation laws give the weighted
raising/lowering commutator and factor the positive hyperbolic Laplacian.
-/

open UpperHalfPlane Complex Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.MaassSmooth
noncomputable section

/-- Smooth complex functions on the upper half-plane, with their actual chart regularity. -/
def space : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | ContDiffOn ℝ ∞ (f ∘ ofComplex) {z : ℂ | 0 < z.im}}
  zero_mem' := contDiffOn_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c

abbrev FunctionSpace := ↥space

instance : CoeFun FunctionSpace (fun _ => ℍ → ℂ) := ⟨fun f => f.1⟩

theorem regular (f : FunctionSpace) :
    ContDiffOn ℝ ∞ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} := f.property

theorem regularAt (f : FunctionSpace) (z : ℍ) :
    ContDiffAt ℝ ∞ ((f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) :=
  (regular f z z.im_pos).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

theorem differentiableAt (f : FunctionSpace) (z : ℍ) :
    DifferentiableAt ℝ ((f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) :=
  (regularAt f z).differentiableAt (by simp)

private theorem chart_directional (f : FunctionSpace) (v : ℂ) :
    ContDiffOn ℝ ∞
      ((fun z : ℍ => fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) v) ∘ ofComplex)
      {z : ℂ | 0 < z.im} := by
  have h := ((regular f).fderiv_of_isOpen isOpen_upperHalfPlaneSet
    (m := ∞) (by simp)).clm_apply (contDiffOn_const (c := v))
  apply h.congr
  intro z hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- Real directional differentiation of the original smooth function. -/
def directional (v : ℂ) : Module.End ℂ FunctionSpace where
  toFun f := ⟨fun z => fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) v,
    chart_directional f v⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (fun w => ((f : ℍ → ℂ) ∘ ofComplex) w + ((g : ℍ → ℂ) ∘ ofComplex) w) (z : ℂ) v =
      fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) v +
        fderiv ℝ ((g : ℍ → ℂ) ∘ ofComplex) (z : ℂ) v
    rw [fderiv_fun_add (differentiableAt f z) (differentiableAt g z)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (fun w => c • ((f : ℍ → ℂ) ∘ ofComplex) w) (z : ℂ) v =
      c • fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) v
    rw [fderiv_fun_const_smul (differentiableAt f z) c]
    rfl

@[simp] theorem directional_apply (v : ℂ) (f : FunctionSpace) (z : ℍ) :
    directional v f z = fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) v := rfl

theorem directional_chart (v : ℂ) (f : FunctionSpace) (z : ℍ) :
    ((directional v f : ℍ → ℂ) ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      (fun w => fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) w v) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, directional_apply, ofComplex_apply_of_im_pos hw]

/-- Mixed directional derivatives commute on the original smooth functions. -/
theorem directional_comm (v w : ℂ) : directional v * directional w = directional w * directional v := by
  ext f z
  change fderiv ℝ ((directional w f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) v =
    fderiv ℝ ((directional v f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) w
  rw [(directional_chart w f z).fderiv_eq, (directional_chart v f z).fderiv_eq]
  have hd := ((regularAt f z).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const w (z : ℂ))).fderiv,
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v (z : ℂ))).fderiv]
  simpa using ((regularAt f z).isSymmSndFDerivAt (by norm_num; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).eq v w

private theorem height_regular : ContDiff ℝ ∞ (fun z : ℂ => (z.im : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff

/-- Multiplication by the imaginary coordinate on actual smooth functions. -/
def height : Module.End ℂ FunctionSpace where
  toFun f := ⟨fun z => (z.im : ℂ) * f z, by
    apply (height_regular.contDiffOn.mul (regular f)).congr
    intro z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]
    rfl⟩
  map_add' f g := by ext z; exact mul_add _ _ _
  map_smul' c f := by ext z; change _ * (c * _) = c * (_ * _); ring

@[simp] theorem height_apply (f : FunctionSpace) (z : ℍ) : height f z = (z.im : ℂ) * f z := rfl

theorem height_chart (f : FunctionSpace) (z : ℍ) :
    ((height f : ℍ → ℂ) ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      (fun w => (w.im : ℂ) * f (ofComplex w)) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, height_apply, ofComplex_apply_of_im_pos hw]
  rfl

/-- The product rule for height and directional differentiation. -/
theorem directional_height (v : ℂ) :
    directional v * height = height * directional v + (v.im : ℂ) • (1 : Module.End ℂ FunctionSpace) := by
  ext f z
  change fderiv ℝ ((height f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) v = _
  rw [(height_chart f z).fderiv_eq]
  have hi : HasFDerivAt (fun w : ℂ => (w.im : ℂ))
      (Complex.ofRealCLM.comp Complex.imCLM) (z : ℂ) :=
    Complex.ofRealCLM.hasFDerivAt.comp _ Complex.imCLM.hasFDerivAt
  have hp := hi.mul (differentiableAt f z).hasFDerivAt
  have hpv := congrArg (fun L => L v) hp.fderiv
  change fderiv ℝ (fun w => (w.im : ℂ) * f (ofComplex w)) (z : ℂ) v = _ at hpv
  rw [hpv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, Function.comp_apply, ofComplex_apply]
  change (z.im : ℂ) * directional v f z + f z * (v.im : ℂ) =
    (z.im : ℂ) * directional v f z + (v.im : ℂ) * f z
  ring

/-- The original Maass cusp function regarded as a smooth function. -/
def ofMaass {Γ : Subgroup SL2R} {lam : ℝ} (f : MaassCuspEigenform Γ lam) : FunctionSpace :=
  ⟨f.1.1, f.contDiffOn⟩

@[simp] theorem ofMaass_apply {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (z : ℍ) : ofMaass f z = f.1.1 z := rfl

theorem ofMaass_ne_zero {Γ : Subgroup SL2R} {lam : ℝ} (f : MaassCuspEigenform Γ lam) :
    ofMaass f ≠ 0 := by
  intro h
  apply f.property.1
  apply Subtype.ext
  exact congrArg (fun g : FunctionSpace => (g : ℍ → ℂ)) h

/-- Two actual directional derivatives in the upper-half-plane chart. -/
theorem directional_directional_apply (v w : ℂ) (f : FunctionSpace) (z : ℍ) :
    directional v (directional w f) z =
      fderiv ℝ (fun u => fderiv ℝ ((f : ℍ → ℂ) ∘ ofComplex) u w) (z : ℂ) v := by
  rw [directional_apply, (directional_chart w f z).fderiv_eq]

theorem directional_height_eq (v : ℂ) (f : FunctionSpace) :
    directional v (height f) = height (directional v f) + (v.im : ℂ) • f :=
  congrArg (fun L : Module.End ℂ FunctionSpace => L f) (directional_height v)

theorem directional_comm_eq (v w : ℂ) (f : FunctionSpace) :
    directional v (directional w f) = directional w (directional v f) :=
  congrArg (fun L : Module.End ℂ FunctionSpace => L f) (directional_comm v w)

/-- Horizontal term in the Maass raising and lowering operators. -/
def X : Module.End ℂ FunctionSpace := Complex.I • (height * directional 1)

/-- Vertical Euler derivative in the Maass raising and lowering operators. -/
def Y : Module.End ℂ FunctionSpace := height * directional Complex.I

theorem X_apply (f : FunctionSpace) : X f = Complex.I • height (directional 1 f) := rfl
theorem Y_apply (f : FunctionSpace) : Y f = height (directional Complex.I f) := rfl

/-- The affine commutator is an identity of actual differential operators. -/
theorem Y_X (f : FunctionSpace) : Y (X f) = X (Y f) + X f := by
  simp only [X_apply, Y_apply, map_smul, directional_height_eq, Complex.I_im,
    Complex.one_im, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul,
    add_zero, map_add, directional_comm_eq Complex.I 1]
  module

theorem X_X (f : FunctionSpace) :
    X (X f) = -height (height (directional 1 (directional 1 f))) := by
  simp only [X_apply, map_smul, directional_height_eq, Complex.one_im,
    Complex.ofReal_zero, zero_smul, add_zero, smul_smul, Complex.I_mul_I, neg_one_smul]

theorem Y_Y (f : FunctionSpace) :
    Y (Y f) = height (height (directional Complex.I (directional Complex.I f))) + Y f := by
  simp only [Y_apply, directional_height_eq, Complex.I_im, Complex.ofReal_one,
    one_smul, map_add]

/-- Raising on the coefficient of a weight `2m` automorphic function. -/
def raise (m : ℤ) : Module.End ℂ FunctionSpace := X - Y - (m : ℂ) • 1

/-- Lowering on the coefficient of a weight `2m` automorphic function. -/
def lower (m : ℤ) : Module.End ℂ FunctionSpace := -X - Y + (m : ℂ) • 1

theorem raise_apply (m : ℤ) (f : FunctionSpace) :
    raise m f = X f - Y f - (m : ℂ) • f := rfl

theorem lower_apply (m : ℤ) (f : FunctionSpace) :
    lower m f = -X f - Y f + (m : ℂ) • f := rfl

/-- The two opposite ladder products differ by the actual weight. -/
theorem raise_lower_comm (m : ℤ) (f : FunctionSpace) :
    raise (m-1) (lower m f) - lower (m+1) (raise m f) = (2 * (m : ℂ)) • f := by
  simp only [raise_apply, lower_apply, map_sub, map_add, map_neg, map_smul, Y_X]
  push_cast
  module

/-- The positive hyperbolic Laplacian on the smooth function space. -/
def laplacian : Module.End ℂ FunctionSpace :=
  -(height * height * (directional 1 * directional 1 + directional Complex.I * directional Complex.I))

@[simp] theorem laplacian_apply (f : FunctionSpace) (z : ℍ) :
    laplacian f z = positiveHyperbolicLaplacian (f : ℍ → ℂ) z := by
  change -((z.im : ℂ) * ((z.im : ℂ) *
    (directional 1 (directional 1 f) z + directional Complex.I (directional Complex.I f) z))) = _
  rw [directional_directional_apply, directional_directional_apply]
  unfold positiveHyperbolicLaplacian
  ring

/-- Factorization of the source Laplacian through actual raising and lowering. -/
theorem lower_raise_zero (f : FunctionSpace) : lower 1 (raise 0 f) = -laplacian f := by
  simp only [lower_apply, raise_apply, Int.cast_zero, Int.cast_one, zero_smul,
    one_smul, sub_zero, map_sub, Y_X, X_X, Y_Y]
  change _ = -(-height (height (directional 1 (directional 1 f) +
    directional Complex.I (directional Complex.I f))))
  rw [neg_neg, map_add, map_add]
  module

/-- The original Maass equation is the eigen-equation of the actual smooth Laplacian. -/
theorem laplacian_ofMaass {Γ : Subgroup SL2R} {lam : ℝ} (f : MaassCuspEigenform Γ lam) :
    laplacian (ofMaass f) = (lam : ℂ) • ofMaass f := by
  apply Subtype.ext
  funext z
  change laplacian (ofMaass f) z = (lam : ℂ) * ofMaass f z
  rw [laplacian_apply]
  exact f.property.2.1.2 z

/-- The source-side Casimir relation at its spherical generator. -/
theorem lower_raise_ofMaass {Γ : Subgroup SL2R} {lam : ℝ} (f : MaassCuspEigenform Γ lam) :
    lower 1 (raise 0 (ofMaass f)) = -(lam : ℂ) • ofMaass f := by
  rw [lower_raise_zero, laplacian_ofMaass]
  module


end
end GaloisForLFunctions.RHTower.MaassSmooth
