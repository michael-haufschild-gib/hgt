import GaloisForLFunctions.HTGeometry.L2DominatedDerivative
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularLocalization

/-! Exact joint cutoff energy for the literal native time primitive in the original
radial/modular measure. Actual chart identities and joint jet continuity establish
compact product integrability before radial/angular Green interchange. The complete
elliptic forcing and cutoff-gradient error are retained; no global native energy or
form-domain premise is used. -/

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMNativeResponse
open D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem chart_line_second (F : ℂ → ℂ)
    (hF : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (l : ℝ → ℂ) (hl : Continuous l) (v : ℂ) (hd : ∀ r, HasDerivAt l v r)
    (a : ℝ) (ha : 0 < (l a).im) :
    fderiv ℝ (fun z => fderiv ℝ F z v) (l a) v = deriv (deriv (fun r => F (l r))) a := by
  have hg := planar_derivative_contDiffOn hF v
  have h0 := ((hg.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds ha)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt a (hd a)
  have he : (fun r => fderiv ℝ F (l r) v) =ᶠ[𝓝 a] deriv (fun r => F (l r)) := by
    have hp : ∀ᶠ r in 𝓝 a, 0 < (l r).im :=
      (isOpen_lt continuous_const (Complex.continuous_im.comp hl)).mem_nhds ha
    filter_upwards [hp] with r hr
    exact (((hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hr)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt r (hd r)).deriv.symm
  exact h0.deriv.symm.trans he.deriv_eq

private theorem positive_chart_laplacian (F : ℂ → ℂ)
    (hF : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) (z : ℂ) (hz : 0 < z.im) :
    planarLaplacian F z =
      deriv (deriv (fun X : ℝ => F ((X:ℂ)+(z.im:ℂ)*Complex.I))) z.re +
      deriv (deriv (fun Y : ℝ => F ((z.re:ℂ)+(Y:ℂ)*Complex.I))) z.im := by
  have hX : ∀ r : ℝ, HasDerivAt (fun X : ℝ => (X:ℂ)+(z.im:ℂ)*Complex.I) 1 r :=
    fun r => by simpa using Complex.ofRealCLM.hasDerivAt.add_const ((z.im:ℂ)*Complex.I)
  have hY : ∀ r : ℝ, HasDerivAt (fun Y : ℝ => (z.re:ℂ)+(Y:ℂ)*Complex.I) Complex.I r :=
    fun r => by simpa using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add (z.re:ℂ)
  have he : (z.re:ℂ)+(z.im:ℂ)*Complex.I=z := Complex.re_add_im z
  have hx := chart_line_second F hF _ (by fun_prop) 1 hX z.re (by simpa only [he] using hz)
  have hy := chart_line_second F hF _ (by fun_prop) Complex.I hY z.im (by simpa only [he] using hz)
  rw [he] at hx hy
  simpa only [planarLaplacian,Fin.sum_univ_two,direction,Matrix.cons_val_zero,Matrix.cons_val_one] using congrArg₂ (·+·) hx hy

private theorem log_second (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (y : ℝ) (hy : 0 < y) :
    (y:ℂ)^2*deriv (deriv (fun r => f (Real.log r))) y =
      deriv (deriv f) (Real.log y)-deriv f (Real.log y) := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hfirst (r : ℝ) (hr : 0 < r) :
      HasDerivAt (fun r => f (Real.log r)) ((r:ℂ)⁻¹*deriv f (Real.log r)) r := by
    convert! (((hf.differentiable (by simp)) (Real.log r)).hasDerivAt.scomp r
      (Real.hasDerivAt_log hr.ne')) using 1
    simp [Complex.real_smul]
  have hsecond := (((Complex.ofRealCLM.hasDerivAt (x := y)).inv
    (by exact_mod_cast hy.ne' : (y:ℂ)≠0)).mul
    (((hf'.differentiable (by simp)) (Real.log y)).hasDerivAt.scomp y
      (Real.hasDerivAt_log hy.ne')))
  have he : deriv (fun r => f (Real.log r)) =ᶠ[𝓝 y]
      (fun r : ℝ => (r:ℂ)⁻¹*deriv f (Real.log r)) := by
    filter_upwards [Ioi_mem_nhds hy] with r hr
    exact (hfirst r hr).deriv
  change HasDerivAt (fun r : ℝ => (r:ℂ)⁻¹*deriv f (Real.log r)) _ y at hsecond
  rw [he.deriv_eq,hsecond.deriv]
  simp only [Pi.inv_apply,Function.comp_apply,Complex.ofRealCLM_apply,Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_one]
  have hyc : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp [hyc]
  ring

private theorem log_chart_smooth (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (fun z : ℂ => f (z.re,Real.log z.im)) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (hf.contDiffAt.comp z (Complex.reCLM.contDiff.contDiffAt.prodMk
    ((Real.contDiffAt_log.mpr hz.ne').comp z Complex.imCLM.contDiff.contDiffAt))).contDiffWithinAt

private theorem log_chart_laplacian (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (z : UpperHalfPlane) :
    chartLaplacian (fun w => f (w.re,Real.log w.im)) z =
      (z.im:ℂ)^2*deriv (deriv (fun X => f (X,Real.log z.im))) z.re +
      deriv (deriv (fun k => f (z.re,k))) (Real.log z.im) -
      deriv (fun k => f (z.re,k)) (Real.log z.im) := by
  let F : ℂ → ℂ := fun w => f (w.re,Real.log w.im)
  have he : (fun w : UpperHalfPlane => f (w.re,Real.log w.im)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] F := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,ofComplex_apply_of_im_pos hw]
    rfl
  have hsecond (v : ℂ) :
      fderiv ℝ (fun w => fderiv ℝ ((fun w : UpperHalfPlane => f (w.re,Real.log w.im)) ∘ ofComplex) w v) (z:ℂ) v =
      fderiv ℝ (fun w => fderiv ℝ F w v) (z:ℂ) v := by
    have hd := he.fderiv (𝕜 := ℝ)
    have hv : (fun w => fderiv ℝ ((fun w : UpperHalfPlane => f (w.re,Real.log w.im)) ∘ ofComplex) w v) =ᶠ[𝓝 (z:ℂ)]
        (fun w => fderiv ℝ F w v) := by
      filter_upwards [hd] with w hw
      rw [hw]
    rw [hv.fderiv_eq]
  have hL : chartLaplacian (fun w => f (w.re,Real.log w.im)) z = (z.im:ℂ)^2*planarLaplacian F z := by
    unfold chartLaplacian planarLaplacian
    simp_rw [hsecond]
  rw [hL,positive_chart_laplacian F (log_chart_smooth f hf) z z.im_pos]
  have hX : (fun X : ℝ => F ((X:ℂ)+(z.im:ℂ)*Complex.I)) = fun X => f (X,Real.log z.im) := by
    funext X
    simp [F]
  have hY : (fun Y : ℝ => F ((z.re:ℂ)+(Y:ℂ)*Complex.I)) = fun Y => f (z.re,Real.log Y) := by
    funext Y
    simp [F]
  change (z.im:ℂ)^2*(deriv (deriv (fun X : ℝ => F ((X:ℂ)+(z.im:ℂ)*Complex.I))) z.re +
    deriv (deriv (fun Y : ℝ => F ((z.re:ℂ)+(Y:ℂ)*Complex.I))) z.im) = _
  have hfY : ContDiff ℝ ∞ (fun k => f (z.re,k)) := hf.comp (contDiff_const.prodMk contDiff_id)
  rw [hX,hY,mul_add,log_second (fun k => f (z.re,k)) hfY z.im z.im_pos]
  ring

private theorem log_chart_frame (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (z : UpperHalfPlane) (v : ℂ) :
    weightedDeriv v (fun w => f (w.re,Real.log w.im)) z =
      (z.im:ℂ)*((v.re:ℂ)*deriv (fun X => f (X,Real.log z.im)) z.re +
        ((v.im/z.im:ℝ):ℂ)*deriv (fun k => f (z.re,k)) (Real.log z.im)) := by
  let F : ℂ → ℂ := fun w => f (w.re,Real.log w.im)
  have he : (fun w : UpperHalfPlane => f (w.re,Real.log w.im)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] F := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,ofComplex_apply_of_im_pos hw]
    rfl
  have hP := Complex.reCLM.hasFDerivAt.prodMk
    ((Real.hasDerivAt_log z.im_pos.ne').hasFDerivAt.comp (z:ℂ) Complex.imCLM.hasFDerivAt)
  have hF := ((hf.differentiable (by simp)) (z.re,Real.log z.im)).hasFDerivAt
  have hc := hF.comp (z:ℂ) hP
  change HasFDerivAt F _ (z:ℂ) at hc
  have hx := hF.comp_hasDerivAt z.re
    ((hasDerivAt_id z.re).prodMk (hasDerivAt_const z.re (Real.log z.im)))
  have hk := hF.comp_hasDerivAt (Real.log z.im)
    ((hasDerivAt_const (Real.log z.im) z.re).prodMk (hasDerivAt_id (Real.log z.im)))
  change HasDerivAt (fun X => f (X,Real.log z.im)) _ z.re at hx
  change HasDerivAt (fun k => f (z.re,k)) _ (Real.log z.im) at hk
  have hv : (v.re,v.im*z.im⁻¹) = v.re • ((1,0):ℝ × ℝ)+(v.im/z.im) • ((0,1):ℝ × ℝ) := by
    ext <;> simp [div_eq_mul_inv,mul_comm]
  unfold weightedDeriv
  rw [he.fderiv_eq,hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    Complex.reCLM_apply,Complex.imCLM_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  rw [hv,map_add,map_smul,map_smul,← hx.deriv,← hk.deriv]
  simp only [Complex.real_smul]

private theorem frame_germ_eq {f g : UpperHalfPlane → ℂ} {z : UpperHalfPlane}
    (he : f =ᶠ[𝓝 z] g) (v : ℂ) : weightedDeriv v f z = weightedDeriv v g z := by
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hp : f ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] g ∘ ofComplex := by
    apply hc.eventually (p := fun w => f w = g w)
    rw [ofComplex_apply]
    exact he
  unfold weightedDeriv
  rw [hp.fderiv_eq]

/-- Both original hyperbolic frame derivatives of the literal primitive are its
actual horizontal and logarithmic-height derivatives on the entire closed cell. -/
theorem nativeTimePrimitive_frame_derivatives (q : XiZeroCopy) (s amplitude : ℂ)
    (t x : ℝ) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    weightedDeriv 1 (globalNativeTimePrimitive q s amplitude t x) z =
      (z.im:ℂ)*deriv (fun X => nativeResidualTimePrimitive q s amplitude t x X (Real.log z.im)) z.re ∧
    weightedDeriv Complex.I (globalNativeTimePrimitive q s amplitude t x) z =
      deriv (fun k => nativeResidualTimePrimitive q s amplitude t x z.re k) (Real.log z.im) := by
  rw [frame_germ_eq (globalNativeTimePrimitive_germ q s amplitude t x z hz),
    frame_germ_eq (globalNativeTimePrimitive_germ q s amplitude t x z hz)]
  rw [log_chart_frame _ (nativeResidualTimePrimitive_angular_smooth q s amplitude t x),
    log_chart_frame _ (nativeResidualTimePrimitive_angular_smooth q s amplitude t x)]
  simp only [Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,zero_div,
    zero_add,add_zero,Complex.ofReal_div]
  constructor
  · trivial
  · have hyc : (z.im:ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
    field_simp [hyc]

/-- The original modular chart Laplacian of the literal native primitive equals its
actual horizontal/log-height derivative expression, including every closed-cell seam. -/
theorem nativeTimePrimitive_chart_laplacian (q : XiZeroCopy) (s amplitude : ℂ)
    (t x : ℝ) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z =
      (z.im:ℂ)^2*deriv (deriv (fun X => nativeResidualTimePrimitive q s amplitude t x X (Real.log z.im))) z.re +
      deriv (deriv (fun k => nativeResidualTimePrimitive q s amplitude t x z.re k)) (Real.log z.im) -
      deriv (fun k => nativeResidualTimePrimitive q s amplitude t x z.re k) (Real.log z.im) := by
  rw [chartLaplacian_congr (globalNativeTimePrimitive_germ q s amplitude t x z hz)]
  exact log_chart_laplacian _ (nativeResidualTimePrimitive_angular_smooth q s amplitude t x) z

/-- The native elliptic equation holds for the original modular chart operator and
the already admitted literal joint forcing, with no form-domain premise. -/
theorem nativeTimePrimitive_original_elliptic_equation (q : XiZeroCopy) (s amplitude : ℂ)
    (t x : ℝ) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    -deriv (deriv (fun r => nativeResidualTimePrimitive q s amplitude t r z.re (Real.log z.im))) x -
      chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z/(Real.cosh x:ℂ)^2 =
      nativeJointEllipticForcing q s amplitude t (x,z) := by
  rw [nativeTimePrimitive_chart_laplacian q s amplitude t x z hz]
  simpa only [Real.exp_log z.im_pos,nativeJointEllipticForcing,nativeJointIntegratedForcing,
    nativeJointResidualField] using
    nativeResidualTimePrimitive_elliptic_equation q s amplitude t x z.re (Real.log z.im)

private abbrev radialJet (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  deriv (fun x => nativeResidualTimePrimitive q s amplitude t x p.2.re (Real.log p.2.im)) p.1
private abbrev radialSecondJet (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  deriv (deriv (fun x => nativeResidualTimePrimitive q s amplitude t x p.2.re (Real.log p.2.im))) p.1
private abbrev horizontalJet (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  (p.2.im:ℂ)*deriv (fun X => nativeResidualTimePrimitive q s amplitude t p.1 X (Real.log p.2.im)) p.2.re
private abbrev heightJet (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  deriv (fun k => nativeResidualTimePrimitive q s amplitude t p.1 p.2.re k) (Real.log p.2.im)
private abbrev laplacianJet (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  (p.2.im:ℂ)^2*deriv (deriv (fun X => nativeResidualTimePrimitive q s amplitude t p.1 X (Real.log p.2.im))) p.2.re +
    deriv (deriv (fun k => nativeResidualTimePrimitive q s amplitude t p.1 p.2.re k)) (Real.log p.2.im) -
    heightJet q s amplitude t p

private theorem jointJets_continuous (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    Continuous (nativeJointTimePrimitiveField q s amplitude t) ∧
    Continuous (radialJet q s amplitude t) ∧ Continuous (radialSecondJet q s amplitude t) ∧
    Continuous (horizontalJet q s amplitude t) ∧ Continuous (heightJet q s amplitude t) ∧
    Continuous (laplacianJet q s amplitude t) := by
  obtain ⟨h0,hx,hxx,hX,hXX,hk,hkk⟩ := nativeResidualTimePrimitive_joint_spatial_jets q s amplitude
  have hlog : Continuous (fun z : UpperHalfPlane => Real.log z.im) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Real.continuousAt_log z.im_pos.ne').comp UpperHalfPlane.continuous_im.continuousAt
  have hc : Continuous (fun p : ℝ × UpperHalfPlane => ((t,p.1),(p.2.re,Real.log p.2.im))) :=
    (continuous_const.prodMk continuous_fst).prodMk
      ((UpperHalfPlane.continuous_re.comp continuous_snd).prodMk (hlog.comp continuous_snd))
  have hy : Continuous (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)) := by fun_prop
  exact ⟨h0.comp hc,hx.comp hc,hxx.comp hc,hy.mul (hX.comp hc),hk.comp hc,
    ((hy.pow 2).mul (hXX.comp hc)).add (hkk.comp hc) |>.sub (hk.comp hc)⟩

private theorem compact_cell_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × UpperHalfPlane → E) (hf : Continuous f) (t N : ℝ)
    (hzero : ∀ p : ℝ × UpperHalfPlane, p.1 < 0 → p.2 ∈ ModularGroup.fd →
      (p.1 < -max t 0-1 ∨ 3*N < p.2.im) → f p = 0) :
    Integrable f (radialMeasure.prod D4BMModularCore.measure) := by
  let K := Icc (-max t 0-1) (0:ℝ) ×ˢ {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ z.im ≤ 3*N}
  have hK : IsCompact K := isCompact_Icc.prod (truncated_cell_compact (3*N))
  have hI := (integrable_indicator_iff hK.measurableSet).mpr
    (hf.continuousOn.integrableOn_compact (μ := radialMeasure.prod D4BMModularCore.measure) hK)
  apply hI.congr
  have hx : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure, p.1 < 0 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Iio)
  have hz : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure, p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [hx,hz] with p hp hfd
  by_cases hpk : p ∈ K
  · simp only [indicator_of_mem hpk]
  · rw [indicator_of_notMem hpk]
    symm
    apply hzero p hp hfd
    by_cases hl : -max t 0-1 ≤ p.1
    · right
      by_contra hh
      apply hpk
      exact ⟨⟨hl,hp.le⟩,hfd,le_of_not_gt hh⟩
    · exact Or.inl (lt_of_not_ge hl)

private theorem native_left_jets_zero (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) (hp : p.1 < -max t 0-1) :
    nativeJointTimePrimitiveField q s amplitude t p = 0 ∧ radialJet q s amplitude t p = 0 ∧
    horizontalJet q s amplitude t p = 0 ∧ heightJet q s amplitude t p = 0 := by
  have hzero (x : ℝ) (hx : x < -max t 0) (X k : ℝ) :
      nativeResidualTimePrimitive q s amplitude t x X k = 0 := by
    apply nativeResidualTimePrimitive_finite_propagation
    have hm := le_max_right t (0:ℝ)
    rw [abs_of_neg (by linarith : x < 0)]
    linarith
  have hp' : p.1 < -max t 0 := by linarith
  have hr : (fun x => nativeResidualTimePrimitive q s amplitude t x p.2.re (Real.log p.2.im)) =ᶠ[𝓝 p.1]
      fun _ => (0:ℂ) := by
    filter_upwards [Iio_mem_nhds hp'] with x hx
    exact hzero x hx _ _
  have hX : (fun X => nativeResidualTimePrimitive q s amplitude t p.1 X (Real.log p.2.im)) = fun _ => (0:ℂ) :=
    funext (fun X => hzero _ hp' X _)
  have hk : (fun k => nativeResidualTimePrimitive q s amplitude t p.1 p.2.re k) = fun _ => (0:ℂ) :=
    funext (fun k => hzero _ hp' _ k)
  exact ⟨hzero _ hp' _ _,by simp only [radialJet,hr.deriv_eq,deriv_const],
    by simp only [horizontalJet,hX,deriv_const,mul_zero],by simp only [heightJet,hk,deriv_const]⟩

private theorem cutoff_high_zero (N : ℝ) (hN : 1 ≤ N) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hy : 3*N < z.im) :
    modularCuspCutoff N z = 0 ∧ ∀ v : ℂ, weightedDeriv v (modularCuspCutoff N) z = 0 := by
  have he : modularCuspCutoff N =ᶠ[𝓝 z] fun _ => (0:ℂ) := by
    apply (modularCuspCutoff_germ N hN z hz).trans
    filter_upwards [(isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds hy] with w hw
    rw [scaledCuspCutoff_high N w.im (by linarith) hw.le,Complex.ofReal_zero]
  refine ⟨he.eq_of_nhds,fun v => ?_⟩
  rw [frame_germ_eq he]
  simp [weightedDeriv,Function.comp_def]

/-- Original radial contribution to the energy of the native field with angular cutoff. -/
def nativeJointRadialCutoffEnergy (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (p : ℝ × UpperHalfPlane) : ℝ :=
  ‖modularCuspCutoff ((n:ℝ)+1) p.2 *
    deriv (fun x => nativeResidualTimePrimitive q s amplitude t x p.2.re (Real.log p.2.im)) p.1‖^2

/-- Original angular contribution, including the exact physical radial weight. -/
def nativeJointAngularCutoffEnergy (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (p : ℝ × UpperHalfPlane) : ℝ :=
  (∑ i : Fin 2, ‖weightedDeriv (direction i)
    (nativeTimePrimitiveCutoff q s amplitude t p.1 n 0).field p.2‖^2) / Real.cosh p.1^2

private theorem native_joint_radial_energy_integrable (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) : Integrable (nativeJointRadialCutoffEnergy q s amplitude t n)
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have hη := (ChartSmooth.continuous (modularCuspCutoff_smooth _ hN)).comp
    (continuous_snd : Continuous (fun p : ℝ × UpperHalfPlane => p.2))
  have hC : Continuous (nativeJointRadialCutoffEnergy q s amplitude t n) :=
    (hη.mul (jointJets_continuous q s amplitude t).2.1).norm.pow 2
  apply compact_cell_integrable _ hC t ((n:ℝ)+1)
  intro p hp hz hh
  rcases hh with hleft|hhigh
  · change ‖modularCuspCutoff ((n:ℝ)+1) p.2*radialJet q s amplitude t p‖^2=0
    rw [(native_left_jets_zero q s amplitude t p hleft).2.1,mul_zero,norm_zero,zero_pow (by simp : (2:ℕ)≠0)]
  · simp only [nativeJointRadialCutoffEnergy,(cutoff_high_zero _ hN p.2 hz hhigh).1,zero_mul,
      norm_zero,zero_pow (by simp : (2:ℕ)≠0)]

private theorem native_joint_cutoff_pairing_integrable (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) (f : ℝ × UpperHalfPlane → ℂ) (hf : Continuous f) :
    Integrable (fun p => conj (f p)*modularCuspCutoff ((n:ℝ)+1) p.2^2*
      nativeJointTimePrimitiveField q s amplitude t p)
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have hη := (ChartSmooth.continuous (modularCuspCutoff_smooth _ hN)).comp
    (continuous_snd : Continuous (fun p : ℝ × UpperHalfPlane => p.2))
  have hC : Continuous (fun p : ℝ × UpperHalfPlane => conj (f p)*modularCuspCutoff ((n:ℝ)+1) p.2^2*
      nativeJointTimePrimitiveField q s amplitude t p) :=
    ((Complex.conjCLE.continuous.comp hf).mul (hη.pow 2)).mul (jointJets_continuous q s amplitude t).1
  apply compact_cell_integrable _ hC t ((n:ℝ)+1)
  intro p hp hz hh
  rcases hh with hleft|hhigh
  · rw [(native_left_jets_zero q s amplitude t p hleft).1,mul_zero]
  · rw [(cutoff_high_zero _ hN p.2 hz hhigh).1,zero_pow (by simp : (2:ℕ)≠0),mul_zero,zero_mul]

private theorem native_cutoff_frame (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ) (n : ℕ)
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    weightedDeriv 1 (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z =
      weightedDeriv 1 (modularCuspCutoff ((n:ℝ)+1)) z*nativeJointTimePrimitiveField q s amplitude t (x,z) +
      modularCuspCutoff ((n:ℝ)+1) z*horizontalJet q s amplitude t (x,z) ∧
    weightedDeriv Complex.I (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z =
      weightedDeriv Complex.I (modularCuspCutoff ((n:ℝ)+1)) z*nativeJointTimePrimitiveField q s amplitude t (x,z) +
      modularCuspCutoff ((n:ℝ)+1) z*heightJet q s amplitude t (x,z) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have h (v : ℂ) : weightedDeriv v (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z =
      weightedDeriv v (modularCuspCutoff ((n:ℝ)+1)) z*globalNativeTimePrimitive q s amplitude t x z +
      modularCuspCutoff ((n:ℝ)+1) z*weightedDeriv v (globalNativeTimePrimitive q s amplitude t x) z := by
    change weightedDeriv v (fun z => modularCuspCutoff ((n:ℝ)+1) z^(0+1)*
      globalNativeTimePrimitive q s amplitude t x z) z = _
    simpa only [Nat.zero_add,pow_one] using weightedDeriv_mul _ _
      (modularCuspCutoff_smooth _ hN) (globalNativeTimePrimitive_smooth q s amplitude t x) v z
  rw [h,h,(globalNativeTimePrimitive_germ q s amplitude t x z hz).eq_of_nhds,
    (nativeTimePrimitive_frame_derivatives q s amplitude t x z hz).1,
    (nativeTimePrimitive_frame_derivatives q s amplitude t x z hz).2]
  exact ⟨rfl,rfl⟩

private theorem native_joint_angular_energy_integrable (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) : Integrable (nativeJointAngularCutoffEnergy q s amplitude t n)
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  let eta := modularCuspCutoff ((n:ℝ)+1)
  let W := nativeJointTimePrimitiveField q s amplitude t
  let E : ℝ × UpperHalfPlane → ℝ := fun p =>
    (‖weightedDeriv 1 eta p.2*W p+eta p.2*horizontalJet q s amplitude t p‖^2+
      ‖weightedDeriv Complex.I eta p.2*W p+eta p.2*heightJet q s amplitude t p‖^2)/Real.cosh p.1^2
  have hη := (ChartSmooth.continuous (modularCuspCutoff_smooth _ hN)).comp
    (continuous_snd : Continuous (fun p : ℝ × UpperHalfPlane => p.2))
  have hd (v : ℂ) : Continuous (fun p : ℝ × UpperHalfPlane => weightedDeriv v eta p.2) :=
    (weightedDeriv_continuous v eta (modularCuspCutoff_smooth _ hN)).comp continuous_snd
  obtain ⟨hW,hx,hxx,hX,hk,hL⟩ := jointJets_continuous q s amplitude t
  have hC : Continuous E :=
    (((((hd 1).mul hW).add (hη.mul hX)).norm.pow 2).add
      ((((hd Complex.I).mul hW).add (hη.mul hk)).norm.pow 2)).div
        (by fun_prop) (fun p => pow_ne_zero 2 (Real.cosh_pos p.1).ne')
  have hI : Integrable E (radialMeasure.prod D4BMModularCore.measure) := by
    apply compact_cell_integrable _ hC t ((n:ℝ)+1)
    intro p hp hz hh
    dsimp only [E,W,eta]
    rcases hh with hleft|hhigh
    · obtain ⟨hw,hr,hX0,hk0⟩ := native_left_jets_zero q s amplitude t p hleft
      rw [hw,hX0,hk0]
      simp
    · obtain ⟨he,hd0⟩ := cutoff_high_zero _ hN p.2 hz hhigh
      rw [he,hd0,hd0]
      simp
  apply hI.congr
  have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure, p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [hfd] with p hp
  simp only [nativeJointAngularCutoffEnergy,Fin.sum_univ_two,direction,Matrix.cons_val_zero,Matrix.cons_val_one,
    (native_cutoff_frame q s amplitude t p.1 n p.2 hp).1,
    (native_cutoff_frame q s amplitude t p.1 n p.2 hp).2]
  rfl

private theorem radial_integral_from_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} (hf : Continuous f) (t : ℝ)
    (hzero : ∀ x < -max t 0-1, f x = 0) :
    Integrable f radialMeasure ∧ (∫ x, f x ∂radialMeasure) = ∫ x in (-max t 0-1)..0, f x := by
  have hI : Integrable f radialMeasure := by
    let K := Icc (-max t 0-1) (0:ℝ)
    have hK : IsCompact K := isCompact_Icc
    apply ((integrable_indicator_iff hK.measurableSet).mpr
      (hf.continuousOn.integrableOn_compact (μ := radialMeasure) hK)).congr
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    by_cases h : x ∈ K
    · simp only [indicator_of_mem h]
    · rw [indicator_of_notMem h,hzero x (by
        by_contra hh
        exact h ⟨le_of_not_gt hh,hx.le⟩)]
  refine ⟨hI,?_⟩
  have hJ : IntegrableOn f (Iio (-max t 0-1)) := by
    have hz : Integrable (fun _ : ℝ => (0:E)) (volume.restrict (Iio (-max t 0-1))) := integrable_zero _ _ _
    apply hz.congr
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact (hzero x hx).symm
  have he := intervalIntegral.integral_Iio_sub_Iio' hI hJ
  have hz : (∫ x in Iio (-max t 0-1), f x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact hzero
  rw [hz,sub_zero] at he
  exact he
private theorem complex_integral_re {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ) :
    (∫ x, (f x).re ∂μ) = (∫ x, f x ∂μ).re := integral_re hf


private abbrev radialPair (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (p : ℝ × UpperHalfPlane) : ℝ :=
  (conj (radialSecondJet q s amplitude t p)*modularCuspCutoff ((n:ℝ)+1) p.2^2*
    nativeJointTimePrimitiveField q s amplitude t p).re
private abbrev angularPair (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (p : ℝ × UpperHalfPlane) : ℝ :=
  (conj (laplacianJet q s amplitude t p)*modularCuspCutoff ((n:ℝ)+1) p.2^2*
    nativeJointTimePrimitiveField q s amplitude t p).re/Real.cosh p.1^2

private theorem real_cutoff_pair (c a b : ℂ) (hc : conj c = c) :
    (conj b*c^2*a).re = ‖c‖^2*(conj a*b).re := by
  have hc0 : c.im = 0 := by
    have h := congrArg Complex.im hc
    simp only [Complex.conj_im] at h
    linarith
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply,pow_two,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,hc0]
  ring

private theorem native_radial_row_energy (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (z : UpperHalfPlane) :
    (∫ x, nativeJointRadialCutoffEnergy q s amplitude t n (x,z) ∂radialMeasure) =
      -∫ x, radialPair q s amplitude t n (x,z) ∂radialMeasure := by
  let W := fun x => nativeResidualTimePrimitive q s amplitude t x z.re (Real.log z.im)
  let c := modularCuspCutoff ((n:ℝ)+1) z
  have hc := modularCuspCutoff_real ((n:ℝ)+1) z
  have hj := jointJets_continuous q s amplitude t
  have hm : Continuous (fun x : ℝ => (x,z)) := continuous_id.prodMk continuous_const
  have hw := hj.1.comp hm
  dsimp only [Function.comp_def,nativeJointTimePrimitiveField] at hw
  change Continuous W at hw
  have hx := hj.2.1.comp hm
  dsimp only [Function.comp_def,radialJet] at hx
  change Continuous (deriv W) at hx
  have hxx := hj.2.2.1.comp hm
  dsimp only [Function.comp_def,radialSecondJet] at hxx
  change Continuous (deriv (deriv W)) at hxx
  have hR : Continuous (fun x => nativeJointRadialCutoffEnergy q s amplitude t n (x,z)) :=
    (hx.const_mul c).norm.pow 2
  have hP : Continuous (fun x => radialPair q s amplitude t n (x,z)) :=
    Complex.continuous_re.comp (((Complex.conjCLE.continuous.comp hxx).mul_const (c^2)).mul hw)
  have hRl : ∀ x < -max t 0-1, nativeJointRadialCutoffEnergy q s amplitude t n (x,z)=0 := by
    intro x hxl
    change ‖modularCuspCutoff ((n:ℝ)+1) z*radialJet q s amplitude t (x,z)‖^2=0
    rw [(native_left_jets_zero q s amplitude t (x,z) hxl).2.1,mul_zero,norm_zero,zero_pow (by simp : (2:ℕ)≠0)]
  have hPl : ∀ x < -max t 0-1, radialPair q s amplitude t n (x,z)=0 := by
    intro x hxl
    simp only [radialPair,(native_left_jets_zero q s amplitude t (x,z) hxl).1,mul_zero,Complex.zero_re]
  rw [(radial_integral_from_interval hR t hRl).2,(radial_integral_from_interval hP t hPl).2]
  have hRP (x : ℝ) : radialPair q s amplitude t n (x,z) = ‖c‖^2*(conj (W x)*deriv (deriv W) x).re :=
    real_cutoff_pair c (W x) (deriv (deriv W) x) hc
  have hRE (x : ℝ) : nativeJointRadialCutoffEnergy q s amplitude t n (x,z) = ‖c‖^2*‖deriv W x‖^2 := by
    change ‖c*deriv W x‖^2 = ‖c‖^2*‖deriv W x‖^2
    rw [norm_mul,mul_pow]
  simp_rw [hRE,hRP]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hr := Complex.reCLM.intervalIntegral_comp_comm
    (((Complex.conjCLE.continuous.comp hw).mul hxx).intervalIntegrable (μ := volume) (-max t 0-1) 0)
  change (∫ x in (-max t 0-1)..0, (conj (W x)*deriv (deriv W) x).re) =
    (∫ x in (-max t 0-1)..0, conj (W x)*deriv (deriv W) x).re at hr
  have hE := nativeResidualTimePrimitive_radial_energy q s amplitude t z.re (Real.log z.im)
  change (∫ x in (-max t 0-1)..0, ‖deriv W x‖^2) =
    -(∫ x in (-max t 0-1)..0, conj (W x)*deriv (deriv W) x).re at hE
  rw [hr,hE]
  ring

private theorem native_radial_pair_integrable (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    Integrable (radialPair q s amplitude t n) (radialMeasure.prod D4BMModularCore.measure) :=
  (native_joint_cutoff_pairing_integrable q s amplitude t n _
    (jointJets_continuous q s amplitude t).2.2.1).re

private theorem native_angular_pair_integrable (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    Integrable (angularPair q s amplitude t n) (radialMeasure.prod D4BMModularCore.measure) := by
  have hC : Continuous (fun p : ℝ × UpperHalfPlane =>
      laplacianJet q s amplitude t p/((Real.cosh p.1^2:ℝ):ℂ)) :=
    (jointJets_continuous q s amplitude t).2.2.2.2.2.div (by fun_prop)
      (fun p => by exact_mod_cast pow_ne_zero 2 (Real.cosh_pos p.1).ne')
  apply (native_joint_cutoff_pairing_integrable q s amplitude t n _ hC).re.congr
  filter_upwards [] with p
  change (conj (laplacianJet q s amplitude t p/((Real.cosh p.1^2:ℝ):ℂ))*
    modularCuspCutoff ((n:ℝ)+1) p.2^2*nativeJointTimePrimitiveField q s amplitude t p).re = _
  rw [map_div₀,Complex.conj_ofReal,div_mul_eq_mul_div,div_mul_eq_mul_div,Complex.div_ofReal_re]

private theorem native_angular_row_energy (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (x : ℝ) :
    (∫ z, nativeJointAngularCutoffEnergy q s amplitude t n (x,z) ∂D4BMModularCore.measure) =
      -(∫ z, angularPair q s amplitude t n (x,z) ∂D4BMModularCore.measure) +
      ∫ z, nativeJointCutoffError q s amplitude t n (x,z)/Real.cosh x^2 ∂D4BMModularCore.measure := by
  let W := globalNativeTimePrimitive q s amplitude t x
  let g := nativeTimePrimitiveCutoff q s amplitude t x n 1
  let P := fun z => conj (chartLaplacian W z)*g.field z
  let err := fun z : UpperHalfPlane => ∑ i : Fin 2,
    ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) z*W z‖^2
  obtain ⟨hE,herr,henergy⟩ := nativeTimePrimitive_compact_angular_localization q s amplitude t x n
  have hP := (nativeTimePrimitive_compact_angular_green q s amplitude t x n).2.1
  have heP : (fun z => angularPair q s amplitude t n (x,z)) =ᵐ[D4BMModularCore.measure]
      (fun z => (P z).re/Real.cosh x^2) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    have hW := (globalNativeTimePrimitive_germ q s amplitude t x z hz).eq_of_nhds
    have hL := nativeTimePrimitive_chart_laplacian q s amplitude t x z hz
    change (conj (laplacianJet q s amplitude t (x,z))*modularCuspCutoff ((n:ℝ)+1) z^2*
      nativeJointTimePrimitiveField q s amplitude t (x,z)).re/Real.cosh x^2 = _
    dsimp only [P,g,nativeTimePrimitiveCutoff,W]
    rw [hL,hW]
    simp only [Nat.reduceAdd,nativeJointTimePrimitiveField]
    congr 2
    ring
  have heE : (fun z => nativeJointCutoffError q s amplitude t n (x,z)) =ᵐ[D4BMModularCore.measure] err := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    dsimp only [err]
    rw [show W z = nativeJointTimePrimitiveField q s amplitude t (x,z) from
      (globalNativeTimePrimitive_germ q s amplitude t x z hz).eq_of_nhds]
    rfl
  have heEw : (fun z => nativeJointCutoffError q s amplitude t n (x,z)/Real.cosh x^2) =ᵐ[D4BMModularCore.measure]
      (fun z => err z/Real.cosh x^2) := by
    filter_upwards [heE] with z hz
    rw [hz]
  have hPr := complex_integral_re (f := P) hP
  change (∫ z, (∑ i : Fin 2, ‖weightedDeriv (direction i)
    (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z‖^2)/Real.cosh x^2
      ∂D4BMModularCore.measure) = _
  rw [integral_div,integral_congr_ae heP,integral_div,
    integral_congr_ae heEw,integral_div,hPr]
  change _ = -((∫ z, P z ∂D4BMModularCore.measure).re/Real.cosh x^2) +
    (∫ z, err z ∂D4BMModularCore.measure)/Real.cosh x^2
  rw [henergy]
  ring

private theorem real_elliptic_pair (a b c : ℂ) (h : ℝ) :
    -(conj a*c).re-(conj b*c).re/h = (conj (-a-b/(h:ℂ))*c).re := by
  simp only [map_sub,map_neg,map_div₀,Complex.conj_ofReal,sub_mul,neg_mul,
    div_mul_eq_mul_div,Complex.sub_re,Complex.neg_re,Complex.div_ofReal_re]

/-- Exact joint cutoff energy identity for the actual native primitive in the original
radial/modular product measure. Both gradient energies and the complete forcing pairing
are integrable. All radial endpoints and modular seams are accounted for before Fubini;
no global energy or form-domain admission is assumed. -/
theorem nativeTimePrimitive_compact_joint_energy (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) :
    Integrable (nativeJointRadialCutoffEnergy q s amplitude t n)
      (radialMeasure.prod D4BMModularCore.measure) ∧
    Integrable (nativeJointAngularCutoffEnergy q s amplitude t n)
      (radialMeasure.prod D4BMModularCore.measure) ∧
    Integrable (fun p : ℝ × UpperHalfPlane => conj (nativeJointEllipticForcing q s amplitude t p)*
      modularCuspCutoff ((n:ℝ)+1) p.2^2*nativeJointTimePrimitiveField q s amplitude t p)
      (radialMeasure.prod D4BMModularCore.measure) ∧
    (∫ p, nativeJointRadialCutoffEnergy q s amplitude t n p+
      nativeJointAngularCutoffEnergy q s amplitude t n p
      ∂radialMeasure.prod D4BMModularCore.measure) =
      (∫ p : ℝ × UpperHalfPlane, conj (nativeJointEllipticForcing q s amplitude t p)*
        modularCuspCutoff ((n:ℝ)+1) p.2^2*nativeJointTimePrimitiveField q s amplitude t p
        ∂radialMeasure.prod D4BMModularCore.measure).re +
      ∫ p : ℝ × UpperHalfPlane, nativeJointCutoffError q s amplitude t n p/Real.cosh p.1^2
        ∂radialMeasure.prod D4BMModularCore.measure := by
  let μ := radialMeasure.prod D4BMModularCore.measure
  let R := nativeJointRadialCutoffEnergy q s amplitude t n
  let A := nativeJointAngularCutoffEnergy q s amplitude t n
  let P := radialPair q s amplitude t n
  let Q := angularPair q s amplitude t n
  let err := fun p : ℝ × UpperHalfPlane => nativeJointCutoffError q s amplitude t n p/Real.cosh p.1^2
  let S := fun p : ℝ × UpperHalfPlane => conj (nativeJointEllipticForcing q s amplitude t p)*
    modularCuspCutoff ((n:ℝ)+1) p.2^2*nativeJointTimePrimitiveField q s amplitude t p
  have hR := native_joint_radial_energy_integrable q s amplitude t n
  have hA := native_joint_angular_energy_integrable q s amplitude t n
  have hP := native_radial_pair_integrable q s amplitude t n
  have hQ := native_angular_pair_integrable q s amplitude t n
  have herr := (nativeJointCutoffError_weighted_tendsto_zero q s amplitude t).1 n
  have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂μ, p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  have hG (p : ℝ × UpperHalfPlane) (hp : p.2 ∈ ModularGroup.fd) :
      -radialSecondJet q s amplitude t p-laplacianJet q s amplitude t p/((Real.cosh p.1^2:ℝ):ℂ) =
        nativeJointEllipticForcing q s amplitude t p := by
    have h := nativeTimePrimitive_original_elliptic_equation q s amplitude t p.1 p.2 hp
    rw [nativeTimePrimitive_chart_laplacian q s amplitude t p.1 p.2 hp] at h
    simpa only [Complex.ofReal_pow] using h
  have hC : Continuous (fun p : ℝ × UpperHalfPlane =>
      -radialSecondJet q s amplitude t p-laplacianJet q s amplitude t p/((Real.cosh p.1^2:ℝ):ℂ)) :=
    (jointJets_continuous q s amplitude t).2.2.1.neg.sub
      ((jointJets_continuous q s amplitude t).2.2.2.2.2.div (by fun_prop)
        (fun p => by exact_mod_cast pow_ne_zero 2 (Real.cosh_pos p.1).ne'))
  have hS : Integrable S μ := by
    apply (native_joint_cutoff_pairing_integrable q s amplitude t n _ hC).congr
    filter_upwards [hfd] with p hp
    rw [hG p hp]
  refine ⟨hR,hA,hS,?_⟩
  have hr : (∫ p, R p ∂μ) = -(∫ p, P p ∂μ) := by
    rw [integral_prod_symm _ hR]
    simp_rw [native_radial_row_energy]
    rw [integral_neg,← integral_prod_symm _ hP]
  have ha : (∫ p, A p ∂μ) = -(∫ p, Q p ∂μ)+(∫ p, err p ∂μ) := by
    rw [integral_prod _ hA]
    simp_rw [native_angular_row_energy]
    have hqi : Integrable (fun x : ℝ => -(∫ z, Q (x,z) ∂D4BMModularCore.measure)) radialMeasure :=
      hQ.integral_prod_left.neg
    have hei : Integrable (fun x : ℝ => ∫ z, err (x,z) ∂D4BMModularCore.measure) radialMeasure :=
      herr.integral_prod_left
    change (∫ x : ℝ, -(∫ z, Q (x,z) ∂D4BMModularCore.measure) +
      (∫ z, err (x,z) ∂D4BMModularCore.measure) ∂radialMeasure) = _
    rw [integral_add hqi hei,integral_neg,← integral_prod _ hQ,← integral_prod _ herr]
  have he : (fun p => -(P p+Q p)) =ᵐ[μ] (fun p => (S p).re) := by
    filter_upwards [hfd] with p hp
    dsimp only [S]
    rw [← hG p hp]
    change -((conj (radialSecondJet q s amplitude t p)*modularCuspCutoff ((n:ℝ)+1) p.2^2*
      nativeJointTimePrimitiveField q s amplitude t p).re+
      (conj (laplacianJet q s amplitude t p)*modularCuspCutoff ((n:ℝ)+1) p.2^2*
        nativeJointTimePrimitiveField q s amplitude t p).re/Real.cosh p.1^2) = _
    simp only [mul_assoc]
    have hh := real_elliptic_pair (radialSecondJet q s amplitude t p) (laplacianJet q s amplitude t p)
      (modularCuspCutoff ((n:ℝ)+1) p.2^2*nativeJointTimePrimitiveField q s amplitude t p) (Real.cosh p.1^2)
    linarith only [hh]
  have hi := integral_congr_ae he
  rw [integral_neg,integral_add hP hQ,complex_integral_re hS] at hi
  change (∫ p, R p+A p ∂μ) = (∫ p, S p ∂μ).re+∫ p, err p ∂μ
  rw [integral_add hR hA,hr,ha]
  linarith only [hi]

/-- The complete source-response pairing is integrable and is the limit of its actual
cusp localizations. This uses only the proved native L² admissions. -/
theorem nativeTimePrimitive_forcing_pairing_limit (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    Integrable (fun p : ℝ × UpperHalfPlane => conj (nativeJointEllipticForcing q s amplitude t p)*
      nativeJointTimePrimitiveField q s amplitude t p) (radialMeasure.prod D4BMModularCore.measure) ∧
    Tendsto (fun n : ℕ => ∫ p : ℝ × UpperHalfPlane,
      conj (nativeJointEllipticForcing q s amplitude t p)*modularCuspCutoff ((n:ℝ)+1) p.2^2*
      nativeJointTimePrimitiveField q s amplitude t p ∂radialMeasure.prod D4BMModularCore.measure)
      atTop (𝓝 (∫ p : ℝ × UpperHalfPlane, conj (nativeJointEllipticForcing q s amplitude t p)*
        nativeJointTimePrimitiveField q s amplitude t p ∂radialMeasure.prod D4BMModularCore.measure)) := by
  let μ := radialMeasure.prod D4BMModularCore.measure
  let W := nativeJointTimePrimitiveField q s amplitude t
  let G := nativeJointEllipticForcing q s amplitude t
  let M := fun p => ‖G p‖^2+‖W p‖^2
  have hW := nativeJointTimePrimitiveField_memLp q s amplitude t
  have hG := nativeJointEllipticForcing_memLp q s amplitude t
  have hM : Integrable M μ := hG.norm.integrable_sq.add hW.norm.integrable_sq
  have hprod (p : ℝ × UpperHalfPlane) : ‖G p‖*‖W p‖ ≤ M p := by
    dsimp only [M]
    nlinarith [sq_nonneg (‖G p‖-‖W p‖),sq_nonneg ‖G p‖,sq_nonneg ‖W p‖]
  have hb (n : ℕ) (p : ℝ × UpperHalfPlane) :
      ‖conj (G p)*modularCuspCutoff ((n:ℝ)+1) p.2^2*W p‖ ≤ M p := by
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_conj]
    have he := modularCuspCutoff_norm_le_one ((n:ℝ)+1) p.2
    have he2 : ‖modularCuspCutoff ((n:ℝ)+1) p.2‖^2 ≤ 1 := by
      nlinarith [norm_nonneg (modularCuspCutoff ((n:ℝ)+1) p.2)]
    calc
      _ ≤ ‖G p‖*1*‖W p‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he2 (norm_nonneg _)) (norm_nonneg _)
      _ ≤ M p := by simpa only [mul_one] using hprod p
  have hm : AEStronglyMeasurable (fun p => conj (G p)*W p) μ :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hG.aestronglyMeasurable).mul hW.aestronglyMeasurable
  refine ⟨hM.mono' hm (Eventually.of_forall fun p => ?_),?_⟩
  · simpa only [norm_mul,Complex.norm_conj] using hprod p
  apply tendsto_integral_of_dominated_convergence M
    (fun n => (nativeTimePrimitive_compact_joint_energy q s amplitude t n).2.2.1.aestronglyMeasurable)
    hM (fun n => Eventually.of_forall (hb n))
  have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂μ, p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [hfd] with p hp
  apply tendsto_const_nhds.congr'
  filter_upwards [modularCuspCutoff_eventually_one p.2 hp] with n hn
  rw [hn.eq_of_nhds]
  simp only [one_pow,mul_one]

/-- The exact localized total energy converges to the full elliptic source pairing,
without presupposing global integrability of any spatial derivative. -/
theorem nativeTimePrimitive_cutoff_energy_limit (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ p, nativeJointRadialCutoffEnergy q s amplitude t n p+
      nativeJointAngularCutoffEnergy q s amplitude t n p ∂radialMeasure.prod D4BMModularCore.measure)
      atTop (𝓝 (∫ p : ℝ × UpperHalfPlane, conj (nativeJointEllipticForcing q s amplitude t p)*
        nativeJointTimePrimitiveField q s amplitude t p ∂radialMeasure.prod D4BMModularCore.measure).re) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (nativeTimePrimitive_forcing_pairing_limit q s amplitude t).2
  have hsum := h.add (nativeJointCutoffError_weighted_tendsto_zero q s amplitude t).2
  simpa only [Function.comp_def,add_zero] using hsum.congr' (Eventually.of_forall
    (fun n => (nativeTimePrimitive_compact_joint_energy q s amplitude t n).2.2.2.symm))

private theorem nonnegative_integral_limit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {L : ℝ}
    (hi : ∀ n, Integrable (F n) μ) (hn : ∀ n, 0 ≤ᵐ[μ] F n)
    (hm : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f)
    (hp : ∀ᵐ p ∂μ, Tendsto (fun n => F n p) atTop (𝓝 (f p)))
    (ht : Tendsto (fun n => ∫ p, F n p ∂μ) atTop (𝓝 L)) :
    Integrable f μ ∧ (∫ p, f p ∂μ) ≤ L := by
  have hmF (n : ℕ) : AEMeasurable (fun p => ENNReal.ofReal (F n p)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hi n).aestronglyMeasurable.aemeasurable
  have hfatou := lintegral_liminf_le' (μ := μ) hmF (u := atTop)
  have hpoint : (fun p => liminf (fun n => ENNReal.ofReal (F n p)) atTop) =ᵐ[μ]
      fun p => ENNReal.ofReal (f p) := by
    filter_upwards [hp] with p hp
    exact (ENNReal.tendsto_ofReal hp).liminf_eq
  have hlim : Tendsto (fun n => ∫⁻ p, ENNReal.ofReal (F n p) ∂μ) atTop
      (𝓝 (ENNReal.ofReal L)) := by
    have h := ENNReal.tendsto_ofReal ht
    apply h.congr'
    exact Eventually.of_forall (fun n => ofReal_integral_eq_lintegral_ofReal (hi n) (hn n))
  rw [lintegral_congr_ae hpoint,hlim.liminf_eq] at hfatou
  have hfinite : HasFiniteIntegral f μ := by
    rw [HasFiniteIntegral]
    have he : (fun p => ENNReal.ofReal ‖f p‖) =ᵐ[μ] fun p => ENNReal.ofReal (f p) := by
      filter_upwards [hf] with p hp
      rw [Real.norm_of_nonneg hp]
    simpa only [← ofReal_norm,lintegral_congr_ae he] using
      lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hfi : Integrable f μ := ⟨hm,hfinite⟩
  have hL : 0 ≤ L := le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall (fun n => integral_nonneg_of_ae (hn n)))
  refine ⟨hfi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hL).mp
  rw [ofReal_integral_eq_lintegral_ofReal hfi hf]
  exact hfatou

/-- The actual radial and hyperbolic first-gradient density of the literal native
primitive, with the original sech² radial weight. -/
def nativeJointGradientEnergy (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) : ℝ :=
  ‖deriv (fun x => nativeResidualTimePrimitive q s amplitude t x p.2.re (Real.log p.2.im)) p.1‖^2 +
    (∑ i : Fin 2, ‖weightedDeriv (direction i)
      (globalNativeTimePrimitive q s amplitude t p.1) p.2‖^2)/Real.cosh p.1^2

private theorem gradient_energy_chart (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) (hp : p.2 ∈ ModularGroup.fd) :
    nativeJointGradientEnergy q s amplitude t p = ‖radialJet q s amplitude t p‖^2+
      (‖horizontalJet q s amplitude t p‖^2+‖heightJet q s amplitude t p‖^2)/Real.cosh p.1^2 := by
  unfold nativeJointGradientEnergy
  simp only [Fin.sum_univ_two,direction,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [(nativeTimePrimitive_frame_derivatives q s amplitude t p.1 p.2 hp).1,
    (nativeTimePrimitive_frame_derivatives q s amplitude t p.1 p.2 hp).2]

private theorem gradient_energy_measurable (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    AEStronglyMeasurable (nativeJointGradientEnergy q s amplitude t)
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hj := jointJets_continuous q s amplitude t
  have hc : Continuous (fun p => ‖radialJet q s amplitude t p‖^2+
      (‖horizontalJet q s amplitude t p‖^2+‖heightJet q s amplitude t p‖^2)/Real.cosh p.1^2) :=
    (hj.2.1.norm.pow 2).add (((hj.2.2.2.1.norm.pow 2).add (hj.2.2.2.2.1.norm.pow 2)).div
      (by fun_prop) (fun p => pow_ne_zero 2 (Real.cosh_pos p.1).ne'))
  apply hc.aestronglyMeasurable.congr
  have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
      p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [hfd] with p hp
  exact (gradient_energy_chart q s amplitude t p hp).symm

private theorem cutoff_energy_pointwise (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) (hp : p.2 ∈ ModularGroup.fd) :
    ∀ᶠ n : ℕ in atTop, nativeJointRadialCutoffEnergy q s amplitude t n p+
      nativeJointAngularCutoffEnergy q s amplitude t n p = nativeJointGradientEnergy q s amplitude t p := by
  filter_upwards [modularCuspCutoff_eventually_one p.2 hp] with n hn
  have he : (nativeTimePrimitiveCutoff q s amplitude t p.1 n 0).field =ᶠ[𝓝 p.2]
      globalNativeTimePrimitive q s amplitude t p.1 := by
    filter_upwards [hn] with z hz
    change modularCuspCutoff ((n:ℝ)+1) z^(0+1)*_ = _
    rw [hz]
    simp
  unfold nativeJointRadialCutoffEnergy nativeJointAngularCutoffEnergy nativeJointGradientEnergy
  rw [hn.eq_of_nhds,one_mul]
  simp only [frame_germ_eq he]

/-- Finite global gradient energy follows from the exact cutoff identities by Fatou.
No native first-derivative integrability or form-domain membership is assumed. -/
theorem nativeTimePrimitive_gradient_energy_integrable (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    Integrable (nativeJointGradientEnergy q s amplitude t)
      (radialMeasure.prod D4BMModularCore.measure) ∧
    (∫ p, nativeJointGradientEnergy q s amplitude t p ∂radialMeasure.prod D4BMModularCore.measure) ≤
      (∫ p : ℝ × UpperHalfPlane, conj (nativeJointEllipticForcing q s amplitude t p)*
        nativeJointTimePrimitiveField q s amplitude t p ∂radialMeasure.prod D4BMModularCore.measure).re := by
  apply nonnegative_integral_limit
    (fun n => (nativeTimePrimitive_compact_joint_energy q s amplitude t n).1.add
      (nativeTimePrimitive_compact_joint_energy q s amplitude t n).2.1)
    (fun n => Eventually.of_forall (fun p => by
      change 0 ≤ nativeJointRadialCutoffEnergy q s amplitude t n p+
        nativeJointAngularCutoffEnergy q s amplitude t n p
      unfold nativeJointRadialCutoffEnergy nativeJointAngularCutoffEnergy
      positivity))
    (gradient_energy_measurable q s amplitude t)
    (Eventually.of_forall (fun p => by unfold nativeJointGradientEnergy; positivity))
    ?_ (nativeTimePrimitive_cutoff_energy_limit q s amplitude t)
  have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
      p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [hfd] with p hp
  apply tendsto_const_nhds.congr'
  filter_upwards [cutoff_energy_pointwise q s amplitude t p hp] with n hn
  exact hn.symm

private theorem square_cutoff_product_bound (c a b : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖a+c*b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have hcb : ‖c*b‖ ≤ ‖b‖ := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg b)
  have hn := (norm_add_le a (c*b)).trans (add_le_add (le_refl ‖a‖) hcb)
  have hs := mul_self_le_mul_self (norm_nonneg (a+c*b)) hn
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

private theorem cutoff_energy_complement_nonnegative (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (n : ℕ) (p : ℝ × UpperHalfPlane) (hp : p.2 ∈ ModularGroup.fd) :
    nativeJointRadialCutoffEnergy q s amplitude t n p+
      nativeJointAngularCutoffEnergy q s amplitude t n p ≤
      2*nativeJointGradientEnergy q s amplitude t p+
        2*(nativeJointCutoffError q s amplitude t n p/Real.cosh p.1^2) := by
  let c := modularCuspCutoff ((n:ℝ)+1) p.2
  let a := weightedDeriv 1 (modularCuspCutoff ((n:ℝ)+1)) p.2*
    nativeJointTimePrimitiveField q s amplitude t p
  let b := weightedDeriv Complex.I (modularCuspCutoff ((n:ℝ)+1)) p.2*
    nativeJointTimePrimitiveField q s amplitude t p
  let h := horizontalJet q s amplitude t p
  let k := heightJet q s amplitude t p
  let r := radialJet q s amplitude t p
  let d := Real.cosh p.1^2
  have hc : ‖c‖ ≤ 1 := modularCuspCutoff_norm_le_one _ _
  have hr : ‖c*r‖^2 ≤ ‖r‖^2 := by
    rw [norm_mul,mul_pow]
    have hc2 : ‖c‖^2 ≤ 1 := by nlinarith [norm_nonneg c]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖r‖)
  have ha := square_cutoff_product_bound c a h hc
  have hb := square_cutoff_product_bound c b k hc
  have hd : 0 ≤ d := sq_nonneg _
  rw [gradient_energy_chart q s amplitude t p hp]
  simp only [nativeJointAngularCutoffEnergy,nativeJointCutoffError,Fin.sum_univ_two,direction,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [(native_cutoff_frame q s amplitude t p.1 n p.2 hp).1,
    (native_cutoff_frame q s amplitude t p.1 n p.2 hp).2]
  change ‖c*r‖^2+(‖a+c*h‖^2+‖b+c*k‖^2)/d ≤
    2*(‖r‖^2+(‖h‖^2+‖k‖^2)/d)+2*((‖a‖^2+‖b‖^2)/d)
  calc
    _ ≤ ‖r‖^2+((2*‖a‖^2+2*‖h‖^2)+(2*‖b‖^2+2*‖k‖^2))/d :=
      add_le_add hr (div_le_div_of_nonneg_right (add_le_add ha hb) hd)
    _ ≤ _ := by
      have he : ‖r‖^2+((2*‖a‖^2+2*‖h‖^2)+(2*‖b‖^2+2*‖k‖^2))/d =
          2*(‖r‖^2+(‖h‖^2+‖k‖^2)/d)+2*((‖a‖^2+‖b‖^2)/d)-‖r‖^2 := by ring
      rw [he]
      exact sub_le_self _ (sq_nonneg _)

/-- Exact global energy identity for the literal native primitive and complete elliptic
forcing in the original measure. A second Fatou argument retains the full cutoff error
and excludes energy escaping through the cusp. -/
theorem nativeTimePrimitive_global_energy (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    (∫ p, nativeJointGradientEnergy q s amplitude t p ∂radialMeasure.prod D4BMModularCore.measure) =
      (∫ p : ℝ × UpperHalfPlane, conj (nativeJointEllipticForcing q s amplitude t p)*
        nativeJointTimePrimitiveField q s amplitude t p ∂radialMeasure.prod D4BMModularCore.measure).re := by
  let μ := radialMeasure.prod D4BMModularCore.measure
  let E := nativeJointGradientEnergy q s amplitude t
  let F := fun n p => nativeJointRadialCutoffEnergy q s amplitude t n p+
    nativeJointAngularCutoffEnergy q s amplitude t n p
  let e := fun n (p : ℝ × UpperHalfPlane) => nativeJointCutoffError q s amplitude t n p/Real.cosh p.1^2
  let L := (∫ p : ℝ × UpperHalfPlane, conj (nativeJointEllipticForcing q s amplitude t p)*
    nativeJointTimePrimitiveField q s amplitude t p ∂μ).re
  have hE : Integrable E μ := (nativeTimePrimitive_gradient_energy_integrable q s amplitude t).1
  have hF (n : ℕ) : Integrable (F n) μ :=
    (nativeTimePrimitive_compact_joint_energy q s amplitude t n).1.add
      (nativeTimePrimitive_compact_joint_energy q s amplitude t n).2.1
  have he (n : ℕ) : Integrable (e n) μ := (nativeJointCutoffError_weighted_tendsto_zero q s amplitude t).1 n
  have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂μ, p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  have hcomp (n : ℕ) : Integrable (fun p => 2*E p+2*e n p-F n p) μ :=
    ((hE.const_mul 2).add ((he n).const_mul 2)).sub (hF n)
  have hnn (n : ℕ) : 0 ≤ᵐ[μ] (fun p => 2*E p+2*e n p-F n p) := by
    filter_upwards [hfd] with p hp
    exact sub_nonneg.mpr (cutoff_energy_complement_nonnegative q s amplitude t n p hp)
  have hpoint : ∀ᵐ p ∂μ, Tendsto (fun n => 2*E p+2*e n p-F n p) atTop (𝓝 (E p)) := by
    filter_upwards [hfd] with p hp
    have hzero : Tendsto (fun n => e n p) atTop (𝓝 (0:ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [modularCuspCutoff_eventually_one p.2 hp] with n hn
      have hz (v : ℂ) : weightedDeriv v (modularCuspCutoff ((n:ℝ)+1)) p.2 = 0 := by
        rw [frame_germ_eq hn]
        unfold weightedDeriv
        change (p.2.im:ℂ)*fderiv ℝ (fun _ : ℂ => (1:ℂ)) (p.2:ℂ) v = 0
        simp
      simp only [e,nativeJointCutoffError,hz,zero_mul,norm_zero,
        zero_pow (by simp : (2:ℕ)≠0),Finset.sum_const_zero,zero_div]
    have hpointF : Tendsto (fun n => F n p) atTop (𝓝 (E p)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_energy_pointwise q s amplitude t p hp] with n hn
      exact hn.symm
    have hc : Tendsto (fun _ : ℕ => 2*E p) atTop (𝓝 (2*E p)) := tendsto_const_nhds
    simpa only [mul_zero,add_zero,two_mul,add_sub_cancel_left] using
      (hc.add (hzero.const_mul 2)).sub hpointF
  have ht : Tendsto (fun n => ∫ p, 2*E p+2*e n p-F n p ∂μ) atTop
      (𝓝 (2*(∫ p, E p ∂μ)-L)) := by
    have ht0 := ((nativeJointCutoffError_weighted_tendsto_zero q s amplitude t).2.const_mul 2)
    have htF := nativeTimePrimitive_cutoff_energy_limit q s amplitude t
    have hc : Tendsto (fun _ : ℕ => 2*(∫ p, E p ∂μ)) atTop
        (𝓝 (2*(∫ p, E p ∂μ))) := tendsto_const_nhds
    have ht := (hc.add ht0).sub htF
    have hi (n : ℕ) : (∫ p, 2*E p+2*e n p-F n p ∂μ) =
        2*(∫ p, E p ∂μ)+2*(∫ p, e n p ∂μ)-(∫ p, F n p ∂μ) := by
      have hs : Integrable (fun p => 2*E p+2*e n p) μ :=
        (hE.const_mul 2).add ((he n).const_mul 2)
      rw [integral_sub hs (hF n),
        integral_add (hE.const_mul 2) ((he n).const_mul 2),integral_const_mul,integral_const_mul]
    simpa only [hi,mul_zero,add_zero] using ht
  have hupper := (nonnegative_integral_limit hcomp hnn hE.aestronglyMeasurable
    (Eventually.of_forall fun p => by unfold E nativeJointGradientEnergy; positivity) hpoint ht).2
  have hlower := (nativeTimePrimitive_gradient_energy_integrable q s amplitude t).2
  change (∫ p, E p ∂μ) = L
  change (∫ p, E p ∂μ) ≤ L at hlower
  linarith only [hlower,hupper]

private theorem continuous_toLp_compact_cell (f : ℝ → UpperHalfPlane → ℂ)
    (hf : ∀ x, MemLp (f x) 2 D4BMModularCore.measure)
    (F : ℝ × UpperHalfPlane → ℂ) (hF : Continuous F)
    (heq : ∀ x z, z ∈ ModularGroup.fd → f x z = F (x,z))
    (a b : ℝ) (K : Set UpperHalfPlane) (hK : IsCompact K)
    (hz : ∀ x z, z ∈ ModularGroup.fd → (x ∉ Icc a b ∨ z ∉ K) → F (x,z) = 0) :
    Continuous (fun x => (hf x).toLp (f x)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hF.continuousOn
  let M := max C 0
  let B := K.indicator (fun _ : UpperHalfPlane => M)
  have hB : MemLp B 2 D4BMModularCore.measure :=
    memLp_indicator_const 2 hK.measurableSet M (Or.inr hK.measure_lt_top.ne)
  apply GaloisForLFunctions.HTGeometry.continuous_toLp_two_of_dominated
    D4BMModularCore.measure f hf B hB
  · intro x
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hfd
    rw [heq x z hfd]
    by_cases hk : z ∈ K
    · rw [show B z = M by exact indicator_of_mem hk _]
      by_cases hx : x ∈ Icc a b
      · exact (hC (x,z) ⟨hx,hk⟩).trans (le_max_left C 0)
      · rw [hz x z hfd (Or.inl hx),norm_zero]
        exact le_max_right C 0
    · rw [show B z = 0 by exact indicator_of_notMem hk _,hz x z hfd (Or.inr hk),norm_zero]
  · filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hfd
    have hc : Continuous (fun x : ℝ => F (x,z)) := hF.comp (continuous_id.prodMk continuous_const)
    exact hc.congr (fun x => (heq x z hfd).symm)

private def nativeAngularSlot (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 3) (x : ℝ) (z : UpperHalfPlane) : ℂ :=
  ![(nativeTimePrimitiveCutoff q s amplitude t x n 0).field z,
    weightedDeriv 1 (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z,
    weightedDeriv Complex.I (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z] i

private def nativeAngularJet (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 3) (p : ℝ × UpperHalfPlane) : ℂ :=
  let η := modularCuspCutoff ((n:ℝ)+1)
  ![η p.2*nativeJointTimePrimitiveField q s amplitude t p,
    weightedDeriv 1 η p.2*nativeJointTimePrimitiveField q s amplitude t p+
      η p.2*horizontalJet q s amplitude t p,
    weightedDeriv Complex.I η p.2*nativeJointTimePrimitiveField q s amplitude t p+
      η p.2*heightJet q s amplitude t p] i

private theorem nativeAngularSlot_memLp (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 3) (x : ℝ) : MemLp (nativeAngularSlot q s amplitude t n i x) 2 D4BMModularCore.measure := by
  let f := nativeTimePrimitiveCutoff q s amplitude t x n 0
  fin_cases i
  · exact core_field_memLp f.field f.smooth f.compact
  · exact weightedDeriv_memLp 1 f.field f.smooth f.compact
  · exact weightedDeriv_memLp Complex.I f.field f.smooth f.compact

private theorem nativeAngularSlot_eq_jet (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 3) (x : ℝ) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    nativeAngularSlot q s amplitude t n i x z = nativeAngularJet q s amplitude t n i (x,z) := by
  fin_cases i
  · change modularCuspCutoff ((n:ℝ)+1) z^(0+1)*globalNativeTimePrimitive q s amplitude t x z = _
    rw [(globalNativeTimePrimitive_germ q s amplitude t x z hz).eq_of_nhds]
    simp only [Nat.zero_add,pow_one,nativeAngularJet]
    rfl
  · exact (native_cutoff_frame q s amplitude t x n z hz).1
  · exact (native_cutoff_frame q s amplitude t x n z hz).2

private theorem nativeAngularJet_continuous (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 3) : Continuous (nativeAngularJet q s amplitude t n i) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have hη := (modularCuspCutoff_smooth _ hN).continuous.comp
    (continuous_snd : Continuous (fun p : ℝ × UpperHalfPlane => p.2))
  have hD (v : ℂ) := (weightedDeriv_continuous v _ (modularCuspCutoff_smooth _ hN)).comp
    (continuous_snd : Continuous (fun p : ℝ × UpperHalfPlane => p.2))
  have hj := jointJets_continuous q s amplitude t
  fin_cases i
  · exact hη.mul hj.1
  · exact ((hD 1).mul hj.1).add (hη.mul hj.2.2.2.1)
  · exact ((hD Complex.I).mul hj.1).add (hη.mul hj.2.2.2.2.1)

private theorem nativeAngularJet_zero_outside (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 3) (x : ℝ) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd)
    (hp : x ∉ Icc (-max t 0-1) (max t 0+1) ∨
      z ∉ {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ z.im ≤ 3*((n:ℝ)+1)}) :
    nativeAngularJet q s amplitude t n i (x,z) = 0 := by
  rcases hp with hx|hk
  · have hx' : max t 0 ≤ |x| := by
      have hm := le_max_right t (0:ℝ)
      by_cases hh : x < -max t 0-1
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · have hhi : max t 0+1 < x := lt_of_not_ge (fun he => hx ⟨le_of_not_gt hh,he⟩)
        rw [abs_of_pos (by linarith : 0 < x)]; linarith
    have hw (X k : ℝ) := nativeResidualTimePrimitive_finite_propagation q s amplitude t x X k hx'
    have hX : (fun X => nativeResidualTimePrimitive q s amplitude t x X (Real.log z.im)) = fun _ => (0:ℂ) :=
      funext (fun X => hw X _)
    have hk : (fun k => nativeResidualTimePrimitive q s amplitude t x z.re k) = fun _ => (0:ℂ) :=
      funext (fun k => hw _ k)
    have hW : nativeJointTimePrimitiveField q s amplitude t (x,z) = 0 := hw _ _
    have hH : horizontalJet q s amplitude t (x,z) = 0 := by simp only [horizontalJet,hX,deriv_const,mul_zero]
    have hK : heightJet q s amplitude t (x,z) = 0 := by simp only [heightJet,hk,deriv_const]
    fin_cases i <;> simp only [nativeAngularJet,hW,hH,hK,mul_zero,add_zero] <;> rfl
  · have hy : 3*((n:ℝ)+1) < z.im := lt_of_not_ge (fun hy => hk ⟨hz,hy⟩)
    have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
      have hn : (0:ℝ) ≤ n := by positivity
      linarith
    obtain ⟨hη,hD⟩ := cutoff_high_zero _ hN z hz hy
    fin_cases i <;> simp only [nativeAngularJet,hη,hD,zero_mul,add_zero] <;> rfl

private theorem nativeAngularSlot_continuous_L2 (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 3) : Continuous (fun x => (nativeAngularSlot_memLp q s amplitude t n i x).toLp
      (nativeAngularSlot q s amplitude t n i x)) :=
  continuous_toLp_compact_cell _ (nativeAngularSlot_memLp q s amplitude t n i)
    _ (nativeAngularJet_continuous q s amplitude t n i)
    (nativeAngularSlot_eq_jet q s amplitude t n i)
    (-max t 0-1) (max t 0+1) _ (truncated_cell_compact (3*((n:ℝ)+1)))
    (nativeAngularJet_zero_outside q s amplitude t n i)

/-- The actual angular energy-domain element at each radius, supplied by its already
constructed native angular core field. -/
def nativeTimePrimitiveAngularEnergy (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (x : ℝ) : D4BMModularCore.energyDomain :=
  ⟨frameGraph (nativeTimePrimitiveCutoff q s amplitude t x n 0),frameGraph_mem _⟩

/-- The actual cusp-cutoff native primitive is a continuous radial family in the
original angular energy norm, including the physical Dirichlet radius. -/
theorem nativeTimePrimitiveAngularEnergy_continuous (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) : Continuous (nativeTimePrimitiveAngularEnergy q s amplitude t n) := by
  apply Continuous.subtype_mk
  change Continuous (fun x => WithLp.toLp 2 ![fieldVector (nativeTimePrimitiveCutoff q s amplitude t x n 0),
    derivativeVector (nativeTimePrimitiveCutoff q s amplitude t x n 0) 1,
    derivativeVector (nativeTimePrimitiveCutoff q s amplitude t x n 0) Complex.I])
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact nativeAngularSlot_continuous_L2 q s amplitude t n 0
  · exact nativeAngularSlot_continuous_L2 q s amplitude t n 1
  · exact nativeAngularSlot_continuous_L2 q s amplitude t n 2

private theorem nativeTimePrimitiveAngularEnergy_zero_of_literal_zero (q : XiZeroCopy)
    (s amplitude : ℂ) (t : ℝ) (n : ℕ) (x : ℝ)
    (h : ∀ X k, nativeResidualTimePrimitive q s amplitude t x X k = 0) :
    nativeTimePrimitiveAngularEnergy q s amplitude t n x = 0 := by
  apply D4BMModularCore.embedding_injective
  rw [map_zero]
  change fieldVector (nativeTimePrimitiveCutoff q s amplitude t x n 0) = 0
  let f := nativeTimePrimitiveCutoff q s amplitude t x n 0
  apply Lp.ext
  filter_upwards [(core_field_memLp f.field f.smooth f.compact).coeFn_toLp,
    Lp.coeFn_zero ℂ 2 D4BMModularCore.measure] with z hz hzero
  rw [show (fieldVector f : UpperHalfPlane → ℂ) z = f.field z from hz,hzero]
  change modularCuspCutoff ((n:ℝ)+1) z^(0+1)*globalNativeTimePrimitive q s amplitude t x z = 0
  simp only [globalNativeTimePrimitive,cellGermExtension,h,mul_zero]

/-- The actual radial family has its Dirichlet trace in the full angular energy norm. -/
theorem nativeTimePrimitiveAngularEnergy_boundary (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) : nativeTimePrimitiveAngularEnergy q s amplitude t n 0 = 0 :=
  nativeTimePrimitiveAngularEnergy_zero_of_literal_zero q s amplitude t n 0
    (nativeResidualTimePrimitive_boundary q s amplitude t)

/-- Finite causal propagation gives compact support of the actual angular-energy-valued
radial family. No mixed derivative estimate is used. -/
theorem nativeTimePrimitiveAngularEnergy_compact (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) : HasCompactSupport (nativeTimePrimitiveAngularEnergy q s amplitude t n) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-max t 0-1) (max t 0+1)) isCompact_Icc
  intro x hx
  by_contra hnot
  have hm := le_max_right t (0:ℝ)
  have hx' : max t 0 ≤ |x| := by
    by_cases hl : x < -max t 0-1
    · rw [abs_of_neg (by linarith : x < 0)]; linarith
    · have hr : max t 0+1 < x := lt_of_not_ge (fun hr => hnot ⟨le_of_not_gt hl,hr⟩)
      rw [abs_of_pos (by linarith : 0 < x)]; linarith
  exact hx (nativeTimePrimitiveAngularEnergy_zero_of_literal_zero q s amplitude t n x
    (fun X k => nativeResidualTimePrimitive_finite_propagation q s amplitude t x X k hx'))

private def nativeCutoffRadial (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (x : ℝ) (z : UpperHalfPlane) : ℂ :=
  modularCuspCutoff ((n:ℝ)+1) z*radialJet q s amplitude t (x,z)

private theorem nativeCutoffRadial_continuous (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × UpperHalfPlane => nativeCutoffRadial q s amplitude t n p.1 p.2) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  exact ((modularCuspCutoff_smooth _ hN).continuous.comp continuous_snd).mul
    (jointJets_continuous q s amplitude t).2.1

private theorem nativeCutoffRadial_zero_outside (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (x : ℝ) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd)
    (hp : x ∉ Icc (-max t 0-1) (max t 0+1) ∨
      z ∉ {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ z.im ≤ 3*((n:ℝ)+1)}) :
    nativeCutoffRadial q s amplitude t n x z = 0 := by
  rcases hp with hx|hk
  · have hx' : max t 0 < |x| := by
      have hm := le_max_right t (0:ℝ)
      by_cases hl : x < -max t 0-1
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · have hr : max t 0+1 < x := lt_of_not_ge (fun hr => hx ⟨le_of_not_gt hl,hr⟩)
        rw [abs_of_pos (by linarith : 0 < x)]; linarith
    have he : (fun y => nativeResidualTimePrimitive q s amplitude t y z.re (Real.log z.im)) =ᶠ[𝓝 x]
        fun _ => (0:ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx'] with y hy
      exact nativeResidualTimePrimitive_finite_propagation q s amplitude t y z.re (Real.log z.im) hy.le
    simp only [nativeCutoffRadial,radialJet,he.deriv_eq,deriv_const,mul_zero]
  · have hy : 3*((n:ℝ)+1) < z.im := lt_of_not_ge (fun hy => hk ⟨hz,hy⟩)
    have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
      have hn : (0:ℝ) ≤ n := by positivity
      linarith
    simp only [nativeCutoffRadial,(cutoff_high_zero _ hN z hz hy).1,zero_mul]

private theorem nativeCutoffRadial_majorant (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    ∃ B : UpperHalfPlane → ℝ, MemLp B 2 D4BMModularCore.measure ∧
      ∀ᵐ z ∂D4BMModularCore.measure, ∀ x, ‖nativeCutoffRadial q s amplitude t n x z‖ ≤ B z := by
  let K := {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ z.im ≤ 3*((n:ℝ)+1)}
  have hK : IsCompact K := truncated_cell_compact _
  have hP : IsCompact (Icc (-max t 0-1) (max t 0+1) ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C,hC⟩ := hP.exists_bound_of_continuousOn
    (nativeCutoffRadial_continuous q s amplitude t n).continuousOn
  let M := max C 0
  refine ⟨K.indicator (fun _ => M),memLp_indicator_const 2 hK.measurableSet M
    (Or.inr hK.measure_lt_top.ne),?_⟩
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  intro x
  by_cases hk : z ∈ K
  · rw [indicator_of_mem hk]
    by_cases hx : x ∈ Icc (-max t 0-1) (max t 0+1)
    · exact (hC (x,z) ⟨hx,hk⟩).trans (le_max_left C 0)
    · rw [nativeCutoffRadial_zero_outside q s amplitude t n x z hz (Or.inl hx),norm_zero]
      exact le_max_right C 0
  · rw [indicator_of_notMem hk,nativeCutoffRadial_zero_outside q s amplitude t n x z hz (Or.inr hk),norm_zero]

private theorem nativeCutoffRadial_memLp (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (x : ℝ) : MemLp (nativeCutoffRadial q s amplitude t n x) 2 D4BMModularCore.measure := by
  obtain ⟨B,hB,hbound⟩ := nativeCutoffRadial_majorant q s amplitude t n
  have hmap : Continuous (fun z : UpperHalfPlane => (x,z)) := continuous_const.prodMk continuous_id
  have hc := (nativeCutoffRadial_continuous q s amplitude t n).comp hmap
  dsimp only [Function.comp_def] at hc
  change Continuous (nativeCutoffRadial q s amplitude t n x) at hc
  exact hB.mono' hc.aestronglyMeasurable (hbound.mono (fun z hz => hz x))

/-- The literal radial derivative of the actual cusp-cutoff primitive, admitted to the
original angular L² space without requiring angular derivatives of this derivative. -/
def nativeTimePrimitiveAngularRadial (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (x : ℝ) : D4BMModularCore.Space :=
  (nativeCutoffRadial_memLp q s amplitude t n x).toLp (nativeCutoffRadial q s amplitude t n x)

private theorem nativeTimePrimitiveAngularRadial_continuous (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) : Continuous (nativeTimePrimitiveAngularRadial q s amplitude t n) :=
  continuous_toLp_compact_cell _ (nativeCutoffRadial_memLp q s amplitude t n)
    _ (nativeCutoffRadial_continuous q s amplitude t n) (fun _ _ _ => rfl)
    (-max t 0-1) (max t 0+1) _ (truncated_cell_compact (3*((n:ℝ)+1)))
    (nativeCutoffRadial_zero_outside q s amplitude t n)

/-- Differentiation of the angular energy family after its original value embedding
has the actual native radial derivative in L². No mixed derivative is assumed. -/
theorem nativeTimePrimitiveAngularEnergy_value_hasDerivAt (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n y))
      (nativeTimePrimitiveAngularRadial q s amplitude t n x) x := by
  obtain ⟨B,hB,hbound⟩ := nativeCutoffRadial_majorant q s amplitude t n
  change HasDerivAt (fun y => (nativeAngularSlot_memLp q s amplitude t n 0 y).toLp
    (nativeAngularSlot q s amplitude t n 0 y))
    ((nativeCutoffRadial_memLp q s amplitude t n x).toLp (nativeCutoffRadial q s amplitude t n x)) x
  apply GaloisForLFunctions.HTGeometry.hasDerivAt_toLp_two_of_dominated D4BMModularCore.measure
    (nativeAngularSlot q s amplitude t n 0) (nativeCutoffRadial q s amplitude t n)
    (nativeAngularSlot_memLp q s amplitude t n 0) (nativeCutoffRadial_memLp q s amplitude t n)
    B hB ?_ hbound x
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  intro y
  have he : (fun y => nativeAngularSlot q s amplitude t n 0 y z) =
      fun y => modularCuspCutoff ((n:ℝ)+1) z*nativeResidualTimePrimitive q s amplitude t y z.re (Real.log z.im) := by
    funext y
    exact nativeAngularSlot_eq_jet q s amplitude t n 0 y z hz
  rw [he]
  exact (nativeResidualTimePrimitive_radial_hasDerivAt q s amplitude t y z.re (Real.log z.im)).1.const_mul _

/-- The original scalar value of the actual angular energy family is C¹ in radius;
this permits classical convolution differentiation inside the Dirichlet half-line. -/
theorem nativeTimePrimitiveAngularEnergy_value_contDiff (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) :
    ContDiff ℝ 1 (fun x => D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x)) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (nativeTimePrimitiveAngularEnergy_value_hasDerivAt q s amplitude t n x).differentiableAt,?_⟩
  have he : deriv (fun x => D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x)) =
      nativeTimePrimitiveAngularRadial q s amplitude t n :=
    funext (fun x => (nativeTimePrimitiveAngularEnergy_value_hasDerivAt q s amplitude t n x).deriv)
  rw [he]
  exact nativeTimePrimitiveAngularRadial_continuous q s amplitude t n

end
end RHTower.D4BMNativeResponse
