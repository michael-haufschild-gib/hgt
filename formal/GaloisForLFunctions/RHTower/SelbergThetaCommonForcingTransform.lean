import GaloisForLFunctions.RHTower.SelbergThetaCommonForcing
import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxSourceWeld
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Entire transform of the actual common theta response

The globally bounded ratio of each actual two-ended Volterra mode to the complete
positive theta source gives absolute Fourier--Laplace convergence at every complex
frequency. Integrating the actual differential equation yields
`(alpha + w) T_q(w) = -XiC(w)` throughout the plane.

The reflected response therefore satisfies
`(alpha^2 - w^2) profileTransform q w = XiC w`.
Its literal integral equals the entire divided-difference expression, including the
removed points. Horizontal-line Fourier continuity supplies those values. These are
the actual response transforms needed in the native scalar contour pairing.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate FourierTransform
namespace RHTower.SelbergThetaCommonForcingTransform
noncomputable section
open SelbergThetaSourcePhase SelbergThetaSourceVariance SelbergThetaCommonForcing
open HedenmalmThetaSource

private theorem parameter_strip (q : XiZeroCopy) : |(xiSpectralPoint q).im| < 1 := by
  have h := xiSpectralPoint_im_mem_openHalf q
  rw [abs_lt]
  constructor <;> linarith

private theorem parameter_ne_zero (q : XiZeroCopy) : xiSpectralPoint q ≠ 0 := by
  intro h
  have hz := mode_orientation q 0
  rw [h,Complex.zero_re,zero_mul] at hz
  exact (lt_irrefl 0) hz

private theorem source_integrable (w : ℂ) :
    Integrable (fun x : ℝ => (thetaCuspFullSource x:ℂ)*Complex.exp (-I*w*(x:ℂ))) := by
  exact (integrable_thetaCuspFourierLaplaceIntegrand_all w).congr
    (Eventually.of_forall fun x => by simp only [thetaCuspFourierLaplaceIntegrand,mul_comm])

private theorem source_transform (w : ℂ) :
    (∫ x : ℝ, (thetaCuspFullSource x:ℂ)*Complex.exp (-I*w*(x:ℂ))) = XiC w := by
  rw [← thetaCuspFourierLaplace_eq_XiC_all,thetaCuspFourierLaplace]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    simp only [thetaCuspFourierLaplaceIntegrand,mul_comm])

/-- Every actual Volterra mode has an absolutely convergent transform at every complex frequency. -/
theorem mode_integrable (q : XiZeroCopy) (w : ℂ) :
    Integrable (fun x : ℝ => mode q x*Complex.exp (-I*w*(x:ℂ))) := by
  obtain ⟨C,hC,hb⟩ := sourceRatio_bounded q
  have hi := (source_integrable w).bdd_mul
    (continuous_sourceRatio q).aestronglyMeasurable (Eventually.of_forall hb)
  refine hi.congr (Eventually.of_forall fun x => ?_)
  have hn : (thetaCuspFullSource x:ℂ) ≠ 0 := by
    exact_mod_cast (thetaCuspFullSource_pos_all x).ne'
  dsimp only
  rw [sourceRatio,← mul_assoc,div_mul_cancel₀ _ hn]

/-- Integrating the literal first-order equation gives the all-plane transform identity. -/
theorem mode_transform_equation (q : XiZeroCopy) (w : ℂ) :
    (xiSpectralPoint q+w)*hedenmalmThetaEigenTransform (xiSpectralPoint q) w = -XiC w := by
  have h1 := (mode_integrable q w).const_mul (-I*(xiSpectralPoint q+w))
  have h2 := (source_integrable w).const_mul I
  have hd : Integrable (fun x : ℝ =>
      (-I*(xiSpectralPoint q+w)*mode q x-I*(thetaCuspFullSource x:ℂ))*
        Complex.exp (-I*w*(x:ℂ))) :=
    (h1.sub h2).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => hasDerivAt_hedenmalmThetaEigen_mul_exp (parameter_strip q) w x)
    hd (mode_integrable q w)
  unfold mode at h1 h2
  have he : (∫ x : ℝ,
      (-I*(xiSpectralPoint q+w)*mode q x-I*(thetaCuspFullSource x:ℂ))*
        Complex.exp (-I*w*(x:ℂ))) =
      -I*(xiSpectralPoint q+w)*hedenmalmThetaEigenTransform (xiSpectralPoint q) w-I*XiC w := by
    rw [← source_transform w,hedenmalmThetaEigenTransform,
      ← integral_const_mul,← integral_const_mul,← integral_sub h1 h2]
    exact integral_congr_ae (Eventually.of_forall fun x => by unfold mode; ring)
  change (∫ x : ℝ,
      (-I*(xiSpectralPoint q+w)*mode q x-I*(thetaCuspFullSource x:ℂ))*
        Complex.exp (-I*w*(x:ℂ))) = 0 at hz
  rw [he] at hz
  linear_combination I*hz+
    ((xiSpectralPoint q+w)*hedenmalmThetaEigenTransform (xiSpectralPoint q) w+XiC w)*I_sq

/-- The literal Fourier--Laplace integral of the reflected common-forcing response. -/
def profileTransform (q : XiZeroCopy) (w : ℂ) : ℂ :=
  ∫ x : ℝ, profile q x*Complex.exp (-I*w*(x:ℂ))

/-- Absolute convergence holds throughout the complex plane for the actual response. -/
theorem profile_integrable (q : XiZeroCopy) (w : ℂ) :
    Integrable (fun x : ℝ => profile q x*Complex.exp (-I*w*(x:ℂ))) := by
  refine ((mode_integrable q w).sub (mode_integrable (xiZeroCopyReflectEquiv q) w)).neg.div_const
    (2*xiSpectralPoint q) |>.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply,Pi.sub_apply,profile]
  ring

private theorem profileTransform_eq_modes (q : XiZeroCopy) (w : ℂ) :
    profileTransform q w = -(hedenmalmThetaEigenTransform (xiSpectralPoint q) w-
      hedenmalmThetaEigenTransform (xiSpectralPoint (xiZeroCopyReflectEquiv q)) w)/(2*xiSpectralPoint q) := by
  have hq := mode_integrable q w
  have hr := mode_integrable (xiZeroCopyReflectEquiv q) w
  unfold mode at hq hr
  rw [profileTransform,hedenmalmThetaEigenTransform,hedenmalmThetaEigenTransform,
    ← integral_sub hq hr,
    ← integral_neg,← integral_div]
  exact integral_congr_ae (Eventually.of_forall fun x => by unfold profile mode; ring)

/-- The exact second-order response identity, without a frequency-strip premise. -/
theorem profile_transform_equation (q : XiZeroCopy) (w : ℂ) :
    ((xiSpectralPoint q)^2-w^2)*profileTransform q w = XiC w := by
  have h1 := mode_transform_equation q w
  have h2 := mode_transform_equation (xiZeroCopyReflectEquiv q) w
  rw [xiSpectralPoint_reflect] at h2
  rw [profileTransform_eq_modes,xiSpectralPoint_reflect]
  field_simp [parameter_ne_zero q]
  linear_combination -(xiSpectralPoint q-w)*h1-(xiSpectralPoint q+w)*h2

/-- The entire divided-difference expression for the common response transform. -/
def entireProfileTransform (q : XiZeroCopy) (w : ℂ) : ℂ :=
  (dslope XiC (-(xiSpectralPoint q)) w-dslope XiC (xiSpectralPoint q) w)/(2*xiSpectralPoint q)

/-- Both divided differences are entire, including their removed points. -/
theorem entireProfileTransform_analytic (q : XiZeroCopy) :
    AnalyticOnNhd ℂ (entireProfileTransform q) univ := by
  have hd (a : ℂ) : DifferentiableOn ℂ (dslope XiC a) univ :=
    (differentiableOn_dslope (isOpen_univ.mem_nhds (mem_univ a))).mpr
      XiC_differentiable.differentiableOn
  intro w _
  exact ((hd _).analyticAt (isOpen_univ.mem_nhds (mem_univ w))).sub
    ((hd _).analyticAt (isOpen_univ.mem_nhds (mem_univ w))) |>.div_const

/-- The divided-difference expression satisfies the actual response equation. -/
theorem entireProfileTransform_equation (q : XiZeroCopy) (w : ℂ) :
    ((xiSpectralPoint q)^2-w^2)*entireProfileTransform q w = XiC w := by
  have h1 := sub_smul_dslope XiC (-(xiSpectralPoint q)) w
  have h2 := sub_smul_dslope XiC (xiSpectralPoint q) w
  rw [XiC_even,XiC_xiSpectralPoint_eq_zero,sub_zero,smul_eq_mul] at h1
  rw [XiC_xiSpectralPoint_eq_zero,sub_zero,smul_eq_mul] at h2
  unfold entireProfileTransform
  field_simp [parameter_ne_zero q]
  linear_combination (xiSpectralPoint q-w)*h1+(xiSpectralPoint q+w)*h2

/-- Away from the two removed points, the response equation identifies the literal transform. -/
theorem profileTransform_eq_entire_of_ne (q : XiZeroCopy) {w : ℂ}
    (hw : (xiSpectralPoint q)^2-w^2 ≠ 0) :
    profileTransform q w = entireProfileTransform q w := by
  exact mul_left_cancel₀ hw ((profile_transform_equation q w).trans
    (entireProfileTransform_equation q w).symm)

def tiltedProfile (q : XiZeroCopy) (a : ℝ) (x : ℝ) : ℂ :=
  profile q x*Complex.exp ((a:ℂ)*(x:ℂ))

theorem tiltedProfile_integrable (q : XiZeroCopy) (a : ℝ) :
    Integrable (tiltedProfile q a) := by
  refine (profile_integrable q ((a:ℂ)*I)).congr (Eventually.of_forall fun x => ?_)
  have he : -I*((a:ℂ)*I)*(x:ℂ) = (a:ℂ)*(x:ℂ) := by
    linear_combination -(a:ℂ)*(x:ℂ)*I_sq
  simp only [he,tiltedProfile]

theorem tiltedProfile_continuous (q : XiZeroCopy) (a : ℝ) :
    Continuous (tiltedProfile q a) :=
  (profile_contDiff q).continuous.mul (by fun_prop)

/-- Exact normalization against mathlib Fourier on every horizontal line. -/
theorem profileTransform_eq_fourier (q : XiZeroCopy) (w : ℂ) :
    profileTransform q w =
      FourierTransform.fourier (tiltedProfile q w.im) (w.re/(2*Real.pi)) := by
  rw [Real.fourier_real_eq,profileTransform]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show profile q x*Complex.exp (-I*w*(x:ℂ)) =
    (Real.fourierChar (-(x*(w.re/(2*Real.pi)))):ℂ) •
      (profile q x*Complex.exp ((w.im:ℂ)*(x:ℂ)))
  rw [Real.fourierChar_apply,smul_eq_mul]
  have hpi : (2*Real.pi:ℝ) ≠ 0 := by positivity
  have he : ((2*Real.pi*(-(x*(w.re/(2*Real.pi)))):ℝ):ℂ) =
      -((x:ℂ)*(w.re:ℂ)) := by
    push_cast
    field_simp
  rw [he,mul_comm (Complex.exp (-((x:ℂ)*(w.re:ℂ))*I))
    (profile q x*Complex.exp ((w.im:ℂ)*(x:ℂ))),
    mul_assoc (profile q x),← Complex.exp_add]
  congr 1
  congr 1
  linear_combination (I*(x:ℂ))*(Complex.re_add_im w)+
    (-(w.im:ℂ)*(x:ℂ))*I_sq

private theorem profileTransform_continuous_line (q : XiZeroCopy) (a : ℝ) :
    Continuous (fun t : ℝ => profileTransform q ((t:ℂ)+(a:ℂ)*I)) := by
  have hc : Continuous (FourierTransform.fourier (tiltedProfile q a)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner (tiltedProfile_integrable q a)
  have he : (fun t : ℝ => profileTransform q ((t:ℂ)+(a:ℂ)*I)) =
      fun t : ℝ => FourierTransform.fourier (tiltedProfile q a) (t/(2*Real.pi)) := by
    ext t
    rw [profileTransform_eq_fourier]
    simp
  rw [he]
  exact hc.comp (by fun_prop)

/-- Fourier continuity identifies the literal transform at both removed points as well. -/
theorem profileTransform_eq_entire (q : XiZeroCopy) (w : ℂ) :
    profileTransform q w = entireProfileTransform q w := by
  have hc := profileTransform_continuous_line q w.im
  have hd : Continuous (fun t : ℝ => entireProfileTransform q ((t:ℂ)+(w.im:ℂ)*I)) :=
    (entireProfileTransform_analytic q).continuous.comp (by fun_prop)
  have he : (fun t : ℝ => profileTransform q ((t:ℂ)+(w.im:ℂ)*I)) =ᵐ[volume]
      fun t : ℝ => entireProfileTransform q ((t:ℂ)+(w.im:ℂ)*I) := by
    filter_upwards [volume.ae_ne (xiSpectralPoint q).re,volume.ae_ne (-(xiSpectralPoint q).re)] with t ht1 ht2
    apply profileTransform_eq_entire_of_ne
    have h1 : xiSpectralPoint q-((t:ℂ)+(w.im:ℂ)*I) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      exact ht1 (by linarith)
    have h2 : xiSpectralPoint q+((t:ℂ)+(w.im:ℂ)*I) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      exact ht2 (by linarith)
    have hf : (xiSpectralPoint q)^2-((t:ℂ)+(w.im:ℂ)*I)^2 =
        (xiSpectralPoint q-((t:ℂ)+(w.im:ℂ)*I))*(xiSpectralPoint q+((t:ℂ)+(w.im:ℂ)*I)) := by ring
    rw [hf]
    exact mul_ne_zero h1 h2
  have h := congrFun ((hc.ae_eq_iff_eq (μ := volume) hd).mp he) w.re
  simpa only [Complex.re_add_im] using h

/-- The actual response integral, rather than only a meromorphic representative, is entire. -/
theorem profileTransform_analytic (q : XiZeroCopy) :
    AnalyticOnNhd ℂ (profileTransform q) univ := by
  have he : profileTransform q = entireProfileTransform q := funext (profileTransform_eq_entire q)
  rw [he]
  exact entireProfileTransform_analytic q

end
end RHTower.SelbergThetaCommonForcingTransform
