import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati
import GaloisForLFunctions.RHTower.HedenmalmThetaEigenODE
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# A global logarithmic coordinate for every actual theta zero mode

Strict logarithmic concavity of the complete theta source makes one of the two tilted tails
strictly decreasing at each spatial point. Its sine transform has a strict sign by integration
by parts against `1 - cos`. At an actual Xi zero the two tails agree, yielding
`Re(z) * Re(u(x)) < 0` for the literal causal Volterra mode, everywhere on the real line.

Consequently `-Re(z) * u` stays in the open right half-plane. Its principal logarithm is globally
differentiable, its logarithmic derivative solves the exact source Riccati equation, and the
associated phase-current density is strictly positive. The complex spectral parameter remains
in that equation. These source theorems do not assert normalized native occurrence or RH.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace RHTower.SelbergThetaSourcePhase
noncomputable section

private theorem schwartz_sine_tail_positive (f : SchwartzMap ℝ ℝ) {b : ℝ}
    (hb : 0 < b) (x : ℝ) (hdec : ∀ t ∈ Ioi x, deriv f t < 0) :
    0 < b * ∫ t in Ioi x, f t * Real.sin (b*(t-x)) := by
  let C : ℝ → ℝ := fun t => 1-Real.cos (b*(t-x))
  let S : ℝ → ℝ := fun t => b*Real.sin (b*(t-x))
  have hCcont : Continuous C := by dsimp [C]; fun_prop
  have hScont : Continuous S := by dsimp [S]; fun_prop
  have hCnorm (t : ℝ) : ‖C t‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [C]; linarith [Real.cos_le_one (b*(t-x))])]
    dsimp [C]
    linarith [Real.neg_one_le_cos (b*(t-x))]
  have hSnorm (t : ℝ) : ‖S t‖ ≤ b := by
    dsimp [S]
    rw [abs_mul, abs_of_pos hb]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hb.le).trans_eq (mul_one b)
  have hFC : Integrable (fun t : ℝ => deriv f t*C t) :=
    (SchwartzMap.derivCLM ℝ ℝ f).integrable.mul_bdd
    hCcont.aestronglyMeasurable (Eventually.of_forall hCnorm)
  have hFS : Integrable (fun t : ℝ => f t*S t) :=
    f.integrable.mul_bdd hScont.aestronglyMeasurable (Eventually.of_forall hSnorm)
  have hderC (t : ℝ) : HasDerivAt C (S t) t := by
    have h := (((hasDerivAt_id t).sub_const x).const_mul b).cos
    simpa [C, S, mul_comm] using h.const_sub 1
  have hprod (t : ℝ) : HasDerivAt (fun u => f u*C u)
      (deriv f t*C t + f t*S t) t := (f.hasDerivAt t).mul (hderC t)
  have hlim : Tendsto (fun t => f t*C t) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun t => 2*‖f t‖)
    · intro t
      rw [norm_mul]
      nlinarith [hCnorm t, norm_nonneg (f t)]
    · simpa using (f.tendsto_cocompact.mono_left atTop_le_cocompact).norm.const_mul 2
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto' (a := x)
    (fun t _ => hprod t) (hFC.add hFS).integrableOn hlim
  have hz : (∫ t in Ioi x, deriv f t*C t) + (∫ t in Ioi x, f t*S t) = 0 := by
    rw [integral_add hFC.integrableOn hFS.integrableOn] at heq
    simpa [C] using heq
  let P : ℝ → ℝ := fun t => -(deriv f t)*C t
  have hPcont : Continuous P := (SchwartzMap.derivCLM ℝ ℝ f).continuous.neg.mul hCcont
  have hPint : Integrable P := by
    convert hFC.neg using 1
    funext t
    dsimp [P]
    ring
  have hPnonneg : 0 ≤ᵐ[volume.restrict (Ioi x)] P := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (neg_nonneg.mpr (hdec t ht).le)
      (by dsimp [C]; linarith [Real.cos_le_one (b*(t-x))])
  have hPt : 0 < P (x+Real.pi/b) := by
    have ht : x < x+Real.pi/b := by linarith [div_pos Real.pi_pos hb]
    have he : b*(x+Real.pi/b-x) = Real.pi := by field_simp; ring
    dsimp [P, C]
    rw [he, Real.cos_pi]
    have hd := hdec (x+Real.pi/b) ht
    nlinarith
  have hpos : 0 < ∫ t in Ioi x, P t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hPnonneg hPint.integrableOn]
    apply IsOpen.measure_pos volume (hPcont.isOpen_support.inter isOpen_Ioi)
    exact ⟨x+Real.pi/b, hPt.ne', by change x < x+Real.pi/b; linarith [div_pos Real.pi_pos hb]⟩
  have hPvalue : (∫ t in Ioi x, P t) = -(∫ t in Ioi x, deriv f t*C t) := by
    change (∫ t in Ioi x, -(deriv f t)*C t) = _
    simp_rw [neg_mul]
    rw [integral_neg]
  have hSvalue : (∫ t in Ioi x, f t*S t) = b * ∫ t in Ioi x, f t*Real.sin (b*(t-x)) := by
    dsimp [S]
    simp_rw [show ∀ t : ℝ, f t*(b*Real.sin (b*(t-x))) = b*(f t*Real.sin (b*(t-x))) by intro t; ring]
    rw [integral_const_mul]
  rw [hPvalue] at hpos
  rw [hSvalue] at hz
  linarith

private def tailIntegrand (f : SchwartzMap ℝ ℝ) (b x t : ℝ) : ℂ :=
  (f t : ℂ) * Complex.exp (I*(b:ℂ)*((t-x:ℝ):ℂ))

private def tailTransform (f : SchwartzMap ℝ ℝ) (b x : ℝ) : ℂ :=
  ∫ t in Ioi x, tailIntegrand f b x t

private theorem tail_integrable (f : SchwartzMap ℝ ℝ) (b x : ℝ) :
    Integrable (tailIntegrand f b x) := by
  have hE : Continuous (fun t : ℝ => Complex.exp (I*(b:ℂ)*((t-x:ℝ):ℂ))) := by fun_prop
  have hnorm (t : ℝ) : ‖Complex.exp (I*(b:ℂ)*((t-x:ℝ):ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  exact f.integrable.ofReal.mul_bdd hE.aestronglyMeasurable (Eventually.of_forall hnorm)

private theorem tail_im (f : SchwartzMap ℝ ℝ) (b x : ℝ) :
    (tailTransform f b x).im = ∫ t in Ioi x, f t * Real.sin (b*(t-x)) := by
  have hi := integral_im (𝕜 := ℂ) (μ := volume.restrict (Ioi x))
    (tail_integrable f b x).integrableOn
  change (∫ t in Ioi x, (tailIntegrand f b x t).im) = (tailTransform f b x).im at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards with t
  simp [tailIntegrand, Complex.mul_im, Complex.mul_re, Complex.exp_im]

private theorem tail_conj (f : SchwartzMap ℝ ℝ) (b x : ℝ) :
    conj (tailTransform f b x) = tailTransform f (-b) x := by
  rw [tailTransform, ← integral_conj, tailTransform]
  apply integral_congr_ae
  filter_upwards with t
  unfold tailIntegrand
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.ofReal_neg,
    Complex.conj_I]
  congr 2
  ring

private def tiltSlope (a x : ℝ) : ℝ := a + deriv thetaCuspLogSource x

private theorem tiltSlope_strictAnti (a : ℝ) : StrictAnti (tiltSlope a) := by
  have hs : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv
        (fun x _ => (hasDerivAt_thetaCuspLogSource x).differentiableAt)
  intro y z h
  simpa [tiltSlope, add_comm] using add_lt_add_left (hs h) a

private theorem tiltSlope_reflect (a x : ℝ) : tiltSlope (-a) (-x) = -tiltSlope a x := by
  have h := iteratedDeriv_thetaCuspLogSource_neg 1 x
  simp only [iteratedDeriv_one, pow_one, neg_one_mul] at h
  simp only [tiltSlope, h]
  ring

private theorem tilted_deriv (a : ℝ) (ha : |a| < 1) (t : ℝ) :
    deriv (thetaCuspTiltedSchwartzReal a ha) t =
      tiltSlope a t * thetaCuspTiltedSchwartzReal a ha t := by
  have hPhi : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource t) t :=
    thetaCuspSchwartzReal.hasDerivAt t
  have h : HasDerivAt (thetaCuspTiltedSource a)
      (Real.exp (a*t)*a*thetaCuspFullSource t + Real.exp (a*t)*deriv thetaCuspFullSource t) t := by
    simpa [thetaCuspTiltedSource, Pi.mul_def] using!
      (((hasDerivAt_id t).const_mul a).exp).mul hPhi
  have hq := (hasDerivAt_thetaCuspLogSource t).deriv
  simp only [iteratedDeriv_one] at hq
  change deriv (thetaCuspTiltedSource a) t = _
  rw [h.deriv]
  change _ = (a + deriv thetaCuspLogSource t) * (Real.exp (a*t)*thetaCuspFullSource t)
  rw [hq]
  have hp := (thetaCuspFullSource_pos_all t).ne'
  field_simp

private theorem tilted_tail_deriv_neg (a : ℝ) (ha : |a| < 1) (x : ℝ)
    (hx : tiltSlope a x ≤ 0) :
    ∀ t ∈ Ioi x, deriv (thetaCuspTiltedSchwartzReal a ha) t < 0 := by
  intro t ht
  rw [tilted_deriv]
  have hs := lt_of_lt_of_le (tiltSlope_strictAnti a ht) hx
  apply mul_neg_of_neg_of_pos hs
  change 0 < Real.exp (a*t)*thetaCuspFullSource t
  exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all t)

private theorem volterra_integrand_eq_tail (z : ℂ) (hz : |z.im| < 1) (x t : ℝ) :
    hedenmalmVolterraIntegrand z x t =
      Complex.exp ((z.im:ℂ)*(x:ℂ)) *
        tailIntegrand (thetaCuspTiltedSchwartzReal (-z.im) (by simpa using hz)) z.re x t := by
  unfold hedenmalmVolterraIntegrand tailIntegrand
  simp only [thetaCuspTiltedSchwartzReal_apply, thetaCuspTiltedSource,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  have he : -I*z*((x:ℂ)-(t:ℂ)) =
      (z.im:ℂ)*(x:ℂ) + (-(z.im:ℂ)*(t:ℂ)) + I*(z.re:ℂ)*((t-x:ℝ):ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [he, Complex.exp_add, Complex.exp_add]
  ring

private theorem anti_eq_tail (z : ℂ) (hz : |z.im| < 1) (x : ℝ) :
    hedenmalmAntiCausalVolterra z x = I * Complex.exp ((z.im:ℂ)*(x:ℂ)) *
      tailTransform (thetaCuspTiltedSchwartzReal (-z.im) (by simpa using hz)) z.re x := by
  rw [hedenmalmAntiCausalVolterra, integral_Ici_eq_integral_Ioi]
  simp_rw [volterra_integrand_eq_tail z hz x]
  rw [integral_const_mul]
  unfold tailTransform
  ring

private theorem tail_orientation (f : SchwartzMap ℝ ℝ) {b : ℝ} (hb : b ≠ 0)
    (x : ℝ) (hdec : ∀ t ∈ Ioi x, deriv f t < 0) :
    0 < b * (tailTransform f b x).im := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have h := schwartz_sine_tail_positive f (neg_pos.mpr hbneg) x hdec
    rw [← tail_im, ← tail_conj, Complex.conj_im] at h
    simpa using h
  · rw [tail_im]
    exact schwartz_sine_tail_positive f hbpos x hdec

private theorem anti_orientation (z : ℂ) (hz : |z.im| < 1) (hb : z.re ≠ 0)
    (x : ℝ) (hx : tiltSlope (-z.im) x ≤ 0) :
    z.re * (hedenmalmAntiCausalVolterra z x).re < 0 := by
  have h := tail_orientation (thetaCuspTiltedSchwartzReal (-z.im) (by simpa using hz))
    hb x (tilted_tail_deriv_neg _ _ _ hx)
  rw [anti_eq_tail z hz x]
  have he : Complex.exp ((z.im:ℂ)*(x:ℂ)) = (Real.exp (z.im*x):ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
  rw [he]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    zero_add, zero_sub]
  have hp := mul_pos (Real.exp_pos (z.im*x)) h
  nlinarith

private theorem integral_Iic_reflect (g : ℝ → ℂ) (x : ℝ) :
    (∫ t in Iic x, g t) = ∫ t in Ici (-x), g (-t) := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ici]
  rw [← integral_neg_eq_self (fun t => (Iic x).indicator g t) volume]
  apply integral_congr_ae
  filter_upwards with t
  change (Iic x).indicator g (-t) = (Ici (-x)).indicator (fun t => g (-t)) t
  by_cases ht : t ∈ Ici (-x)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show -t ∈ Iic x by
      simp only [mem_Ici] at ht; simp only [mem_Iic]; linarith)]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show -t ∉ Iic x by
      simp only [mem_Ici] at ht; simp only [mem_Iic]; linarith)]

private theorem causal_reflect (z : ℂ) (x : ℝ) :
    hedenmalmCausalVolterra z x = -hedenmalmAntiCausalVolterra (-z) (-x) := by
  rw [hedenmalmCausalVolterra, integral_Iic_reflect, hedenmalmAntiCausalVolterra]
  have he (t : ℝ) : hedenmalmVolterraIntegrand z x (-t) =
      hedenmalmVolterraIntegrand (-z) (-x) t := by
    unfold hedenmalmVolterraIntegrand
    rw [thetaCuspFullSource_neg]
    congr 2
    push_cast
    ring
  simp_rw [he]
  ring

private theorem causal_orientation_of_zero (z : ℂ) (hz : |z.im| < 1)
    (hb : z.re ≠ 0) (hzero : XiC z = 0) (x : ℝ) :
    z.re * (hedenmalmCausalVolterra z x).re < 0 := by
  by_cases hx : tiltSlope (-z.im) x ≤ 0
  · rw [(hedenmalmCausalVolterra_eq_antiCausal_iff hz).2 hzero x]
    exact anti_orientation z hz hb x hx
  · have hzneg : |(-z).im| < 1 := by simpa using hz
    have hbneg : (-z).re ≠ 0 := by simpa using hb
    have hs : tiltSlope (-(-z).im) (-x) ≤ 0 := by
      simp only [Complex.neg_im, neg_neg]
      have he := tiltSlope_reflect (-z.im) x
      simp only [neg_neg] at he
      rw [he]
      linarith
    have h := anti_orientation (-z) hzneg hbneg (-x) hs
    rw [causal_reflect]
    simpa only [Complex.neg_re, neg_mul, mul_neg] using h

/-- The literal two-ended theta mode at an actual multiplicity copy of the Xi divisor. -/
def mode (q : XiZeroCopy) (x : ℝ) : ℂ :=
  hedenmalmCausalVolterra (xiSpectralPoint q) x

private theorem parameter_strip (q : XiZeroCopy) : |(xiSpectralPoint q).im| < 1 := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  rw [abs_lt]
  simp [xiSpectralPoint, Complex.mul_im]
  constructor <;> linarith

private theorem parameter_re_ne_zero (q : XiZeroCopy) : (xiSpectralPoint q).re ≠ 0 := by
  simpa [xiSpectralPoint, Complex.mul_im, Complex.mul_re] using
    xi_divisor_support_im_ne_zero q.1

/-- Every actual mode has a strictly oriented real part at every spatial point. -/
theorem mode_orientation (q : XiZeroCopy) (x : ℝ) :
    (xiSpectralPoint q).re * (mode q x).re < 0 :=
  causal_orientation_of_zero _ (parameter_strip q) (parameter_re_ne_zero q)
    (XiC_xiSpectralPoint_eq_zero q) x

/-- The actual mode has no spatial zeros, without a critical-line assumption. -/
theorem mode_ne_zero (q : XiZeroCopy) (x : ℝ) : mode q x ≠ 0 := by
  intro hx
  have h := mode_orientation q x
  rw [hx, Complex.zero_re, mul_zero] at h
  exact (lt_irrefl 0) h

/-- Normalize the actual mode by its nonzero real spectral frequency. -/
def positiveMode (q : XiZeroCopy) (x : ℝ) : ℂ :=
  -((xiSpectralPoint q).re:ℂ) * mode q x

/-- The normalized actual mode lies in the open right half-plane everywhere. -/
theorem positiveMode_re_pos (q : XiZeroCopy) (x : ℝ) : 0 < (positiveMode q x).re := by
  have h := mode_orientation q x
  simpa [positiveMode, Complex.mul_re] using neg_pos.mpr h


/-- The exact first-order theta source equation, at the actual divisor parameter. -/
theorem hasDerivAt_mode (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (mode q)
      (-I * xiSpectralPoint q * mode q x - I * (thetaCuspFullSource x : ℂ)) x :=
  hasDerivAt_hedenmalmCausalVolterra (parameter_strip q) x

/-- The source formula for the global logarithmic derivative of the actual mode. -/
def modeLogDerivative (q : XiZeroCopy) (x : ℝ) : ℂ :=
  -I * xiSpectralPoint q - I * (thetaCuspFullSource x : ℂ) / mode q x

/-- The source expression equals the ordinary logarithmic derivative everywhere. -/
theorem modeLogDerivative_eq (q : XiZeroCopy) (x : ℝ) :
    modeLogDerivative q x = deriv (mode q) x / mode q x := by
  rw [(hasDerivAt_mode q x).deriv]
  unfold modeLogDerivative
  field_simp [mode_ne_zero q x]

/-- Global Riccati equation, retaining the complete complex spectral parameter. -/
theorem hasDerivAt_modeLogDerivative (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (modeLogDerivative q)
      ((((deriv thetaCuspLogSource x : ℝ) : ℂ) - modeLogDerivative q x) *
        (modeLogDerivative q x + I * xiSpectralPoint q)) x := by
  have hp : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource x) x :=
    thetaCuspSchwartzReal.hasDerivAt x
  have h := ((hp.ofReal_comp.const_mul I).div (hasDerivAt_mode q x)
    (mode_ne_zero q x)).const_sub (-I * xiSpectralPoint q)
  have hq := (hasDerivAt_thetaCuspLogSource x).deriv
  simp only [iteratedDeriv_one] at hq
  have he : ((deriv thetaCuspFullSource x : ℝ) : ℂ) =
      ((deriv thetaCuspLogSource x : ℝ) : ℂ) * (thetaCuspFullSource x : ℂ) := by
    rw [hq]
    push_cast
    field_simp [(thetaCuspFullSource_pos_all x).ne']
  refine h.congr_deriv ?_
  rw [he]
  unfold modeLogDerivative
  field_simp [mode_ne_zero q x]
  ring

/-- The canonical principal logarithm of the actual right-half-plane mode. -/
def modeLog (q : XiZeroCopy) (x : ℝ) : ℂ := Complex.log (positiveMode q x)

/-- The principal logarithm differentiates globally to the actual source ratio. -/
theorem hasDerivAt_modeLog (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (modeLog q) (modeLogDerivative q x) x := by
  have h := ((hasDerivAt_mode q x).const_mul (-((xiSpectralPoint q).re : ℂ))).clog_real
    (Complex.mem_slitPlane_iff.mpr (Or.inl (positiveMode_re_pos q x)))
  refine h.congr_deriv ?_
  have hb : ((xiSpectralPoint q).re : ℂ) ≠ 0 := by
    exact_mod_cast parameter_re_ne_zero q
  unfold modeLogDerivative
  field_simp [mode_ne_zero q x, hb]


/-- Exact source-density formula for the shifted phase derivative. -/
theorem mode_phase_current (q : XiZeroCopy) (x : ℝ) :
    (xiSpectralPoint q).re * ((modeLogDerivative q x).im + (xiSpectralPoint q).re) =
      (positiveMode q x).re * thetaCuspFullSource x / Complex.normSq (mode q x) := by
  simp [modeLogDerivative, positiveMode, Complex.mul_im, Complex.mul_re, Complex.div_im]
  ring

/-- The shifted phase current is strictly positive at every actual zero and spatial point. -/
theorem mode_phase_current_pos (q : XiZeroCopy) (x : ℝ) :
    0 < (xiSpectralPoint q).re * ((modeLogDerivative q x).im + (xiSpectralPoint q).re) := by
  rw [mode_phase_current]
  exact div_pos (mul_pos (positiveMode_re_pos q x) (thetaCuspFullSource_pos_all x))
    (Complex.normSq_pos.mpr (mode_ne_zero q x))

end
end RHTower.SelbergThetaSourcePhase
