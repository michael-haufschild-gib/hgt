import GaloisForLFunctions.RHTower.SelbergThetaNativeContour
import GaloisForLFunctions.RHTower.SelbergThetaCommonForcingPairing

/-!
# Native theta pairing as an arithmetic Cauchy transform

The logarithmic height substitution identifies the literal native pairing with
an absolutely admitted Fourier product. Its two actual Fourier transforms give
the right vertical contour in `SelbergThetaNativeContour`, including all constants.

Reflection of the entire common-forcing response replaces the complete scattering
phase under the boundary integral by `boundaryWeight`. The resulting Cauchy formula
holds at every actual Xi copy, with absolute convergence; the possible real removed
points are handled by equality almost everywhere. The original constant-mode
correction remains explicit in `sourcePairing_cauchy`.

These identities expose the native scalar cancellation target. They do not establish
its reality, the required retained-mass packets, or the Riemann hypothesis.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate FourierTransform
namespace RHTower.SelbergThetaNativeScalarBoundary
noncomputable section
open SelbergThetaCommonForcing SelbergThetaCommonForcingTransform
open SelbergThetaCommonForcingPairing SelbergThetaHorizontalTransform
open SelbergThetaHorizontalBoundary SelbergThetaNativeContour

private def sourceLine (t : ℝ) : ℂ := 1/4+(t:ℂ)*I
private def sourceParameter (t : ℝ) : D4BMEisensteinAbsoluteConvergenceParameter :=
  ⟨1+sourceLine t/2,by dsimp [sourceLine]; norm_num⟩

/-- The literal horizontal source on the absolutely convergent quarter line. -/
def safeSource (x : ℝ) : ℂ :=
  Complex.exp ((x:ℂ)/4)*(horizontalWeight (Real.exp (2*x)):ℂ)

private theorem logIntegrand_parameter (t x : ℝ) :
    logIntegrand (sourceParameter t) (-2*x) =
      Complex.exp (I*(t:ℂ)*(x:ℂ))*safeSource x := by
  unfold logIntegrand sourceParameter sourceLine safeSource
  have he : -(1+((1/4:ℂ)+(t:ℂ)*I)/2-1)*((-2*x:ℝ):ℂ) =
      I*(t:ℂ)*(x:ℂ)+(x:ℂ)/4 := by push_cast; ring
  rw [he,Complex.exp_add]
  have hr : -(-2*x) = 2*x := by ring
  rw [hr]
  ring

theorem safeSource_integrable : Integrable safeSource := by
  have h := (logIntegrand_integrable (sourceParameter 0)).comp_mul_left' (R := (-2:ℝ)) (by norm_num)
  simpa only [logIntegrand_parameter,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,one_mul] using h

private theorem integral_logIntegrand_parameter (t : ℝ) :
    (∫ x, logIntegrand (sourceParameter t) x) = 2*symbol (sourceLine t) := by
  rw [integral_logIntegrand,symbol_eq_source (by simp [sourceLine])]
  have h0 : 2*(sourceParameter t).s-1/2 = sourceLine t+3/2 := by dsimp [sourceParameter]; ring
  have h1 : 2*(sourceParameter t).s-1 = sourceLine t+1 := by dsimp [sourceParameter]; ring
  have h2 : 2*(sourceParameter t).s = sourceLine t+2 := by dsimp [sourceParameter]; ring
  rw [h0,h1,h2]
  ring

theorem safeSource_fourier (t : ℝ) :
    FourierTransform.fourier safeSource (-t/(2*Real.pi)) = symbol (sourceLine t) := by
  have he : FourierTransform.fourier safeSource (-t/(2*Real.pi)) =
      ∫ x : ℝ, Complex.exp (I*(t:ℂ)*(x:ℂ))*safeSource x := by
    rw [Real.fourier_real_eq]
    apply integral_congr_ae (Eventually.of_forall fun x => ?_)
    change (Real.fourierChar (-(x*(-t/(2*Real.pi)))):ℂ) • safeSource x =
      Complex.exp (I*(t:ℂ)*(x:ℂ))*safeSource x
    rw [Real.fourierChar_apply,smul_eq_mul]
    have hpi : (2*Real.pi:ℝ) ≠ 0 := by positivity
    have ha : ((2*Real.pi*(-(x*(-t/(2*Real.pi)))):ℝ):ℂ) = (x:ℂ)*(t:ℂ) := by
      push_cast
      field_simp
    rw [ha]
    congr 1
    congr 1
    ring
  rw [he]
  simp_rw [← logIntegrand_parameter]
  rw [Measure.integral_comp_mul_left,integral_logIntegrand_parameter]
  norm_num [Complex.real_smul]
  ring

private def responseLine (t : ℝ) : ℂ := (t:ℂ)-(5/4:ℂ)*I

private theorem responseLine_xi (t : ℝ) : XiC (responseLine t) = xi (7/4+(t:ℂ)*I) := by
  unfold XiC responseLine
  congr 1
  linear_combination -(5/4:ℂ)*I_sq

private theorem responseLine_denominator (q : XiZeroCopy) (t : ℝ) :
    (1/2:ℝ) ≤ ‖(xiSpectralPoint q)^2-(responseLine t)^2‖ := by
  have hs := xiSpectralPoint_im_mem_openHalf q
  have hw : (responseLine t).im = -5/4 := by norm_num [responseLine]
  have h1 : (3/4:ℝ) ≤ ‖xiSpectralPoint q-responseLine t‖ := by
    have hh := Complex.abs_im_le_norm (xiSpectralPoint q-responseLine t)
    rw [Complex.sub_im,hw] at hh
    have ha := le_abs_self ((xiSpectralPoint q).im-(-5/4))
    linarith
  have h2 : (3/4:ℝ) ≤ ‖xiSpectralPoint q+responseLine t‖ := by
    have hh := Complex.abs_im_le_norm (xiSpectralPoint q+responseLine t)
    rw [Complex.add_im,hw] at hh
    have ha := le_abs_self (-((xiSpectralPoint q).im+(-5/4)))
    rw [abs_neg] at ha
    linarith
  have he : (xiSpectralPoint q)^2-(responseLine t)^2 =
      (xiSpectralPoint q-responseLine t)*(xiSpectralPoint q+responseLine t) := by ring
  rw [he,norm_mul]
  have hh := mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 3/4) (norm_nonneg _)
  linarith

private theorem responseLine_bound (q : XiZeroCopy) (t : ℝ) :
    ‖profileTransform q (responseLine t)‖ ≤ 2*‖xi (7/4+(t:ℂ)*I)‖ := by
  have he := congrArg norm (profile_transform_equation q (responseLine t))
  rw [norm_mul,responseLine_xi] at he
  have hb := responseLine_denominator q t
  nlinarith [norm_nonneg (profileTransform q (responseLine t))]

private theorem responseLine_integrable (q : XiZeroCopy) :
    Integrable (fun t : ℝ => profileTransform q (responseLine t)) := by
  have hc : Continuous (fun t : ℝ => profileTransform q (responseLine t)) :=
    (profileTransform_analytic q).continuous.comp (by unfold responseLine; fun_prop)
  exact ((xi_line_integrable (c := (7/4:ℝ)) (by norm_num) (by norm_num)).norm.const_mul 2).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun t => by simpa using responseLine_bound q t)

private theorem tiltedProfile_fourier (q : XiZeroCopy) (u : ℝ) :
    FourierTransform.fourier (tiltedProfile q (-5/4)) u =
      profileTransform q (responseLine (2*Real.pi*u)) := by
  have h := profileTransform_eq_fourier q (responseLine (2*Real.pi*u))
  have hr : (responseLine (2*Real.pi*u)).re = 2*Real.pi*u := by norm_num [responseLine]
  have hi : (responseLine (2*Real.pi*u)).im = -5/4 := by norm_num [responseLine]
  have hu : (2*Real.pi*u)/(2*Real.pi) = u := by field_simp
  rw [hr,hi,hu] at h
  exact h.symm

theorem tiltedProfile_fourier_integrable (q : XiZeroCopy) :
    Integrable (FourierTransform.fourier (tiltedProfile q (-5/4))) := by
  have h := (responseLine_integrable q).comp_mul_left' (R := 2*Real.pi) (by positivity)
  exact h.congr (Eventually.of_forall fun u => by simpa only [mul_assoc] using (tiltedProfile_fourier q u).symm)

private theorem integral_product_fourier {F G : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G)
    (hFT : Integrable (FourierTransform.fourier F)) (hFc : Continuous F) :
    (∫ x, F x*G x) = ∫ u, FourierTransform.fourier F u*FourierTransform.fourier G (-u) := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hFT hG.comp_neg
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by ext; simp
  rw [hflip] at h
  change (∫ x, FourierTransform.fourier (FourierTransform.fourier F) x*G (-x)) =
    ∫ u, FourierTransform.fourier F u*FourierTransform.fourier (fun x => G (-x)) u at h
  have hinv := hFc.fourierInv_fourier_eq hF hFT
  have hff (x : ℝ) : FourierTransform.fourier (FourierTransform.fourier F) x = F (-x) := by
    have hh := congrFun hinv (-x)
    rwa [Real.fourierInv_eq_fourier_neg,neg_neg] at hh
  have hgf (x : ℝ) : FourierTransform.fourier (fun x => G (-x)) x =
      FourierTransform.fourier G (-x) := by
    have hh := congrFun (Real.fourierInv_eq_fourier_comp_neg G) x
    rw [Real.fourierInv_eq_fourier_neg] at hh
    exact hh.symm
  simp_rw [hff,hgf] at h
  change (∫ x, (fun y => F y*G y) (-x)) = _ at h
  exact (integral_neg_eq_self (fun y : ℝ => F y*G y) volume).symm.trans h

private theorem product_exp (q : XiZeroCopy) (x : ℝ) :
    tiltedProfile q (-5/4) x*safeSource x =
      (Complex.exp (x:ℂ))⁻¹*(profile q x*(horizontalWeight (Real.exp (2*x)):ℂ)) := by
  unfold tiltedProfile safeSource
  have he : Complex.exp (((-5/4:ℝ):ℂ)*(x:ℂ))*Complex.exp ((x:ℂ)/4) =
      (Complex.exp (x:ℂ))⁻¹ := by
    rw [← Complex.exp_add,← Complex.exp_neg]
    congr 1
    push_cast
    ring
  calc _ = (Complex.exp (((-5/4:ℝ):ℂ)*(x:ℂ))*Complex.exp ((x:ℂ)/4))*
            (profile q x*(horizontalWeight (Real.exp (2*x)):ℂ)) := by ring
       _ = _ := by rw [he]

private theorem heightPair_exp (q : XiZeroCopy) (x : ℝ) :
    |2*Real.exp (2*x)| • ((Real.exp (2*x))^2)⁻¹ •
      (heightProfile q (Real.exp (2*x))*(horizontalWeight (Real.exp (2*x)):ℂ)) =
      2*(tiltedProfile q (-5/4) x*safeSource x) := by
  rw [abs_of_pos (by positivity),product_exp,heightProfile,Real.log_exp]
  have hx : (2*x)/2 = x := by ring
  rw [hx]
  have he : (Real.exp (2*x):ℂ) = (Complex.exp (x:ℂ))^2 := by
    rw [Complex.ofReal_exp]
    have hh : ((2*x:ℝ):ℂ) = (x:ℂ)+(x:ℂ) := by push_cast; ring
    rw [hh,Complex.exp_add,pow_two]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_inv,Complex.ofReal_pow]
  rw [he,Complex.ofReal_exp]
  field_simp [Complex.exp_ne_zero (x:ℂ)]

/-- The native height integral in its exact logarithmic half-density normalization. -/
theorem scalarResponse_eq_log_pairing (q : XiZeroCopy) :
    scalarResponse q = 2*∫ x, tiltedProfile q (-5/4) x*safeSource x := by
  have himg : (fun x : ℝ => Real.exp (2*x)) '' univ = Ioi (0:ℝ) := by
    ext y
    simp only [mem_image,mem_univ,true_and,mem_Ioi]
    constructor
    · rintro ⟨x,rfl⟩
      exact Real.exp_pos _
    · intro hy
      refine ⟨Real.log y/2,?_⟩
      have hh : 2*(Real.log y/2) = Real.log y := by ring
      rw [hh,Real.exp_log hy]
  have hinj : InjOn (fun x : ℝ => Real.exp (2*x)) univ := by
    intro x _ y _ h
    have hh := Real.exp_injective h
    linarith
  have hd (x : ℝ) (_ : x ∈ univ) :
      HasDerivWithinAt (fun y : ℝ => Real.exp (2*y)) (2*Real.exp (2*x)) univ x := by
    simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using
      ((Real.hasDerivAt_exp (2*x)).comp x ((hasDerivAt_id x).const_mul 2)).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := fun x : ℝ => Real.exp (2*x)) (f' := fun x : ℝ => 2*Real.exp (2*x))
    (s := univ) MeasurableSet.univ hd hinj
    (fun y : ℝ => (y^2)⁻¹ • (heightProfile q y*(horizontalWeight y:ℂ)))
  rw [himg,setIntegral_univ] at h
  change scalarResponse q = _ at h
  rw [h,← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => heightPair_exp q x)

private theorem fourier_product_eq_responseSymbol (q : XiZeroCopy) (u : ℝ) :
    FourierTransform.fourier (tiltedProfile q (-5/4)) u*FourierTransform.fourier safeSource (-u) =
      responseSymbol q (sourceLine (2*Real.pi*u)) := by
  have hg := safeSource_fourier (2*Real.pi*u)
  have hu : -(2*Real.pi*u)/(2*Real.pi) = -u := by field_simp
  rw [hu] at hg
  have he (t : ℝ) : -I*(sourceLine t+1) = responseLine t := by
    unfold sourceLine responseLine
    linear_combination -(t:ℂ)*I_sq
  rw [tiltedProfile_fourier,hg,responseSymbol_eq_product,he]
  ring

private theorem integral_responseSymbol_scaled (q : XiZeroCopy) :
    (∫ u : ℝ, responseSymbol q (sourceLine (2*Real.pi*u))) =
      VerticalIntegral' (responseSymbol q) (1/4) := by
  change (∫ u : ℝ, (fun t : ℝ => responseSymbol q (sourceLine t)) ((2*Real.pi)*u)) = _
  calc
    _ = |(2*Real.pi)⁻¹| • ∫ t : ℝ, responseSymbol q (sourceLine t) :=
      Measure.integral_comp_mul_left (fun t : ℝ => responseSymbol q (sourceLine t)) (2*Real.pi)
    _ = _ := by
      rw [abs_of_pos (by positivity : (0:ℝ) < (2*Real.pi)⁻¹)]
      simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_ofNat,
        VerticalIntegral',VerticalIntegral,smul_eq_mul,sourceLine]
      field_simp
      apply integral_congr_ae
      filter_upwards [] with t
      congr 1
      push_cast
      ring

/-- Bilinear Fourier duality identifies the actual native pairing with the safe contour. -/
theorem scalarResponse_eq_contour (q : XiZeroCopy) :
    scalarResponse q = 2*VerticalIntegral' (responseSymbol q) (1/4) := by
  rw [scalarResponse_eq_log_pairing,integral_product_fourier
    (tiltedProfile_integrable q (-5/4)) safeSource_integrable
    (tiltedProfile_fourier_integrable q) (tiltedProfile_continuous q (-5/4))]
  simp_rw [fourier_product_eq_responseSymbol]
  rw [integral_responseSymbol_scaled]

/-- The source-response contour transfer, now joined to the literal native scalar. -/
theorem scalarResponse_spectral_boundary (q : XiZeroCopy) :
    scalarResponse q =
      2*mainTerm*xi (3/2)/(1+(xiSpectralPoint q)^2)+
      (1/(Real.pi:ℂ))*∫ t : ℝ,
        XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ) := by
  rw [scalarResponse_eq_contour,responseSymbol_spectral_boundary]
  ring

/-- The literal response transform has the source's real-frequency reflection symmetry. -/
theorem profileTransform_even_real (q : XiZeroCopy) (t : ℝ) :
    profileTransform q ((-t:ℝ):ℂ) = profileTransform q (t:ℂ) := by
  have hc : Continuous (fun t : ℝ => profileTransform q (t:ℂ)) :=
    (profileTransform_analytic q).continuous.comp Complex.continuous_ofReal
  have he : (fun t : ℝ => profileTransform q ((-t:ℝ):ℂ)) =ᵐ[volume]
      fun t : ℝ => profileTransform q (t:ℂ) := by
    filter_upwards [volume.ae_ne (xiSpectralPoint q).re,
      volume.ae_ne (-(xiSpectralPoint q).re)] with t ht1 ht2
    have h1 : xiSpectralPoint q-(t:ℂ) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      exact ht1 (by linarith)
    have h2 : xiSpectralPoint q+(t:ℂ) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      exact ht2 (by linarith)
    have hn : (xiSpectralPoint q)^2-(t:ℂ)^2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero h2 h1
    have hh := profile_transform_equation q (-(t:ℂ))
    rw [neg_sq,XiC_even] at hh
    simpa only [Complex.ofReal_neg] using
      mul_left_cancel₀ hn (hh.trans (profile_transform_equation q (t:ℂ)).symm)
  exact congrFun (((hc.comp continuous_neg).ae_eq_iff_eq (μ := volume) hc).mp he) t

private theorem boundary_reflection_average (q : XiZeroCopy) (t : ℝ) :
    XiC (t:ℂ)*(boundaryWeight t:ℂ)*profileTransform q (t:ℂ) =
      (XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ)+
       XiC ((-t:ℝ):ℂ)*(1+boundaryPhase (-t))*profileTransform q ((-t:ℝ):ℂ))/2 := by
  rw [profileTransform_even_real,boundaryPhase_neg,Complex.ofReal_neg,XiC_even]
  have hc : (boundaryWeight t:ℂ) =
      ((1+boundaryPhase t)+(1+conj (boundaryPhase t)))/2 := by
    apply Complex.ext <;> simp [boundaryWeight]
  rw [hc]
  ring

/-- Absolute convergence is retained when the full scattering phase is symmetrized. -/
theorem real_boundary_integrable (q : XiZeroCopy) :
    Integrable (fun t : ℝ => XiC (t:ℂ)*(boundaryWeight t:ℂ)*profileTransform q (t:ℂ)) := by
  have h := responseSymbol_boundary_integrable q
  exact ((h.add h.comp_neg).div_const 2).congr
    (Eventually.of_forall fun t => (boundary_reflection_average q t).symm)

/-- The complete boundary integral equals its real arithmetic-weight expression. -/
theorem boundary_integral_eq_real (q : XiZeroCopy) :
    (∫ t : ℝ, XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ)) =
      ∫ t : ℝ, XiC (t:ℂ)*(boundaryWeight t:ℂ)*profileTransform q (t:ℂ) := by
  have h := responseSymbol_boundary_integrable q
  have hr := integral_neg_eq_self
    (fun t : ℝ => XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ)) volume
  have ha : (∫ t : ℝ, XiC (t:ℂ)*(boundaryWeight t:ℂ)*profileTransform q (t:ℂ)) =
      ((∫ t : ℝ, XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ))+
       ∫ t : ℝ, XiC ((-t:ℝ):ℂ)*(1+boundaryPhase (-t))*profileTransform q ((-t:ℝ):ℂ))/2 := by
    simp_rw [boundary_reflection_average]
    rw [integral_div,integral_add h h.comp_neg]
  rw [hr] at ha
  linear_combination -ha

/-- Exact spectral formula for the original native scalar response, including its mean residue. -/
theorem scalarResponse_real_boundary (q : XiZeroCopy) :
    scalarResponse q =
      2*mainTerm*xi (3/2)/(1+(xiSpectralPoint q)^2)+
      (1/(Real.pi:ℂ))*∫ t : ℝ,
        XiC (t:ℂ)*(boundaryWeight t:ℂ)*profileTransform q (t:ℂ) := by
  rw [scalarResponse_spectral_boundary,boundary_integral_eq_real]

/-- The actual positive source mass equals the off-axis theta transform. -/
theorem sourceMass_eq_xi : (SelbergThetaNativeSource.sourceMass:ℂ) = 2*xi (3/2) := by
  have he (x : ℝ) : (Real.exp (-x):ℂ)*(thetaCuspFullSource x:ℂ) =
      thetaCuspFourierLaplaceIntegrand (-I) x := by
    rw [thetaCuspFourierLaplaceIntegrand,Complex.ofReal_exp,Complex.ofReal_neg]
    congr 2
    linear_combination -(x:ℂ)*I_sq
  have hx : XiC (-I) = xi (3/2) := by norm_num [XiC,I_sq]
  rw [SelbergThetaNativeSource.sourceMass,Complex.ofReal_mul,Complex.ofReal_ofNat,
    ← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul,he]
  rw [← thetaCuspFourierLaplace,HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all,hx]

private theorem real_boundary_ae_cauchy (q : XiZeroCopy) :
    (fun t : ℝ => XiC (t:ℂ)*(boundaryWeight t:ℂ)*profileTransform q (t:ℂ)) =ᵐ[volume]
      fun t : ℝ => -((Xi t:ℂ)^2*(boundaryWeight t:ℂ)/((t:ℂ)^2-(xiSpectralPoint q)^2)) := by
  filter_upwards [volume.ae_ne (xiSpectralPoint q).re,
    volume.ae_ne (-(xiSpectralPoint q).re)] with t ht1 ht2
  have h1 : xiSpectralPoint q-(t:ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact ht1 (by linarith)
  have h2 : xiSpectralPoint q+(t:ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact ht2 (by linarith)
  have hn : (xiSpectralPoint q)^2-(t:ℂ)^2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero h2 h1
  have he : profileTransform q (t:ℂ) = XiC (t:ℂ)/((xiSpectralPoint q)^2-(t:ℂ)^2) :=
    (eq_div_iff hn).mpr (by simpa only [mul_comm] using profile_transform_equation q (t:ℂ))
  rw [he,XiC_ofReal]
  have hd : (t:ℂ)^2-(xiSpectralPoint q)^2 = -((xiSpectralPoint q)^2-(t:ℂ)^2) := by ring
  rw [hd,div_neg,neg_neg]
  ring

/-- Absolute admission of the literal arithmetic Cauchy integral at every actual Xi copy. -/
theorem native_cauchy_integrable (q : XiZeroCopy) :
    Integrable (fun t : ℝ =>
      (Xi t:ℂ)^2*(boundaryWeight t:ℂ)/((t:ℂ)^2-(xiSpectralPoint q)^2)) := by
  have h := (real_boundary_integrable q).congr (real_boundary_ae_cauchy q)
  exact h.neg.congr (Eventually.of_forall fun t => by simp only [Pi.neg_apply,neg_neg])

/-- The native scalar response is a mean residue plus the complete arithmetic Cauchy transform. -/
theorem scalarResponse_cauchy (q : XiZeroCopy) :
    scalarResponse q =
      2*mainTerm*xi (3/2)/(1+(xiSpectralPoint q)^2)-
      (1/(Real.pi:ℂ))*∫ t : ℝ,
        (Xi t:ℂ)^2*(boundaryWeight t:ℂ)/((t:ℂ)^2-(xiSpectralPoint q)^2) := by
  rw [scalarResponse_real_boundary,integral_congr_ae (real_boundary_ae_cauchy q),integral_neg]
  ring

/-- The actual constant-mode correction and arithmetic Cauchy transform in one native equality. -/
theorem sourcePairing_cauchy (q : XiZeroCopy) :
    SelbergThetaCommonForcingGram.sourcePairing q =
      -(1/4:ℂ)*(2*mainTerm*xi (3/2)/(1+(xiSpectralPoint q)^2)-
        (SelbergThetaNativeSource.sourceMass:ℂ)^2/
          ((1+(xiSpectralPoint q)^2)*inner ℂ SelbergNativeConstantMode.constantVector
            SelbergNativeConstantMode.constantVector))+
      (1/(4*(Real.pi:ℂ)))*∫ t : ℝ,
        (Xi t:ℂ)^2*(boundaryWeight t:ℂ)/((t:ℂ)^2-(xiSpectralPoint q)^2) := by
  rw [sourcePairing_eq_scalarResponse,scalarResponse_cauchy]
  ring

end
end RHTower.SelbergThetaNativeScalarBoundary
