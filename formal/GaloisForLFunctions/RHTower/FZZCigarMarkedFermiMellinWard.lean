import GaloisForLFunctions.RHTower.FZZCigarFermiCouplingExchange
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Analytic.Order

/-!
# Original marked Fermi source under the Mellin transform

The first replica derivative is integrated against the exponential log-coupling
law before taking its positive-delay Mellin transform. For every positive radial
slope, the resulting transform is a nonvanishing analytic multiple of the Fermi
Mellin divisor. Its spectral derivative is the convergent original logarithmic
insertion. The exact zero-set, local-order and joint-vanishing classifications
follow without a source-vanishing assumption.

These identities do not identify this radial source with the complete compact
winding correlator, establish its physical coupling law, or fix the external
phase frame. Positive-delay endpoint limits are not target-radial finite parts.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.RHTower
noncomputable section

def fzzFermiMarkedDelay (t : ℝ) : ℂ :=
  ∫ u : ℝ, (fzzExponentialLogCouplingDensity u : ℂ) *
    deriv (fun δ => fzzMarkedRadialReplicaIntegrand u 0 0 δ t) 0

def fzzFermiMarkedMellin (s : ℂ) : ℂ := mellin fzzFermiMarkedDelay s

private theorem radial_zero (u t : ℝ) :
    fzzMarkedRadialReplicaIntegrand u 0 0 0 t = (fzzRadialCouplingDensity u 0 t : ℂ) := by
  simp [fzzMarkedRadialReplicaIntegrand, fzzRadialCouplingDensity,
    fzzNeutralRadialKernel, fzzNeutralRadialCoordinate, Real.exp_sub, Real.exp_neg,
    div_eq_mul_inv]

private theorem radial_jet (u t : ℝ) :
    deriv (fun δ => fzzMarkedRadialReplicaIntegrand u 0 0 δ t) 0 =
      (-3*(t : ℂ))*(fzzRadialCouplingDensity u 0 t : ℂ) := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaIntegrand u 0 0 t).deriv, radial_zero]
  norm_num [fzzMarkedRadialReplicaRate]

theorem integrable_fzzFermiMarkedDelay_integrand (t : ℝ) :
    Integrable (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      deriv (fun δ => fzzMarkedRadialReplicaIntegrand u 0 0 δ t) 0) := by
  have hi : Integrable (fun u : ℝ => (-3*(t : ℂ))*
      ((fzzExponentialLogCouplingDensity u * fzzRadialCouplingDensity u 0 t : ℝ) : ℂ)) :=
    (integrable_fzzFermiCouplingDensity_integrand 0 t).ofReal.const_mul (-3*(t : ℂ))
  apply hi.congr
  filter_upwards with u
  rw [radial_jet, Complex.ofReal_mul]
  ring

theorem fzzFermiMarkedDelay_eq (t : ℝ) :
    fzzFermiMarkedDelay t = (-3*(t : ℂ))*(_root_.RHTower.logisticKernel t : ℂ) := by
  have he : (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      deriv (fun δ => fzzMarkedRadialReplicaIntegrand u 0 0 δ t) 0) =
      fun u : ℝ => (-3*(t : ℂ))*
        ((fzzExponentialLogCouplingDensity u * fzzRadialCouplingDensity u 0 t : ℝ) : ℂ) := by
    funext u
    rw [radial_jet, Complex.ofReal_mul]
    ring
  rw [fzzFermiMarkedDelay, he, integral_const_mul, integral_complex_ofReal]
  change (-3*(t : ℂ))*(fzzFermiCouplingDensity 0 t : ℂ) = _
  rw [fzzFermiCouplingDensity_eq, Real.exp_zero, one_mul, one_mul]

private theorem fermi_deriv (t : ℝ) :
    HasDerivAt _root_.RHTower.salemFermiKernel (-(_root_.RHTower.logisticKernel t : ℂ)) t := by
  have h := (hasDerivAt_fzzFermiCouplingAverage 0 t).ofReal_comp
  have hf : (fun x : ℝ => (fzzFermiCouplingAverage 0 x : ℂ)) =
      _root_.RHTower.salemFermiKernel := by
    funext x
    simp only [fzzFermiCouplingAverage_eq, Real.exp_zero, one_mul,
      _root_.RHTower.salemFermiKernel, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_one, add_comm]
  rw [hf] at h
  simpa only [fzzFermiCouplingDensity_eq, Real.exp_zero, one_mul, Complex.ofReal_neg] using! h

private theorem logistic_exp_bound (t : ℝ) :
    _root_.RHTower.logisticKernel t ≤ Real.exp (-t) := by
  have he := Real.exp_pos t
  have hc : Real.exp t * Real.exp t ≤ (1 + Real.exp t)^2 := by nlinarith
  rw [_root_.RHTower.logisticKernel, Real.exp_neg]
  calc
    Real.exp t/(1+Real.exp t)^2 ≤ Real.exp t/(Real.exp t*Real.exp t) :=
      div_le_div_of_nonneg_left he.le (mul_pos he he) hc
    _ = (Real.exp t)⁻¹ := by field_simp

private theorem gamma_dominated_integrable (g : ℝ → ℂ) (hc : Continuous g)
    (hb : ∀ t : ℝ, ‖g t‖ ≤ Real.exp (-t)) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(s-1)*g t) (Ioi 0) := by
  apply (Real.GammaIntegral_convergent hs).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul _ hc.continuousOn
    intro t ht
    exact ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr ht)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simpa only [Complex.sub_re, Complex.one_re, mul_comm] using
      mul_le_mul_of_nonneg_left (hb t) (Real.rpow_nonneg ht.le (s.re-1))

private theorem fermi_weight_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(s-1)*_root_.RHTower.salemFermiKernel t) (Ioi 0) :=
  gamma_dominated_integrable _ _root_.RHTower.continuous_salemFermiKernel
    _root_.RHTower.norm_salemFermiKernel_le_exp_neg hs

private theorem logistic_weight_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^s*(_root_.RHTower.logisticKernel t : ℂ)) (Ioi 0) := by
  have hi := gamma_dominated_integrable (fun t => (_root_.RHTower.logisticKernel t : ℂ))
    (Complex.continuous_ofReal.comp _root_.RHTower.continuous_logisticKernel)
    (fun t => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (_root_.RHTower.logisticKernel_pos t)]
      exact logistic_exp_bound t) (s := s+1) (by simpa using (show 0 < s.re+1 by linarith))
  simpa only [add_sub_cancel_right] using hi

private theorem boundary_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => (t : ℂ)^s*_root_.RHTower.salemFermiKernel t) (𝓝[>] 0) (𝓝 0) := by
  have h := ((Complex.continuous_ofReal_cpow_const hs).mul
    _root_.RHTower.continuous_salemFermiKernel).tendsto 0
  have hn : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl _ hs
  simpa only [Pi.mul_apply, Complex.ofReal_zero, Complex.zero_cpow hn, zero_mul]
    using! h.mono_left inf_le_left

private theorem boundary_infty (s : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ)^s*_root_.RHTower.salemFermiKernel t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _))
    (show ∀ᶠ t : ℝ in atTop,
      ‖(t : ℂ)^s*_root_.RHTower.salemFermiKernel t‖ ≤ t^s.re*Real.exp (-1*t) from ?_)
  · exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s.re 1 zero_lt_one
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, neg_one_mul]
    exact mul_le_mul_of_nonneg_left (_root_.RHTower.norm_salemFermiKernel_le_exp_neg t)
      (Real.rpow_nonneg ht.le _)

private theorem logistic_mellin_identity {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ)^s*(_root_.RHTower.logisticKernel t : ℂ)) =
      s * _root_.RHTower.fzzCigarParityMellin s := by
  have hn : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl _ hs
  have ha : IntegrableOn (fun t : ℝ => (t : ℂ)^s*(-(_root_.RHTower.logisticKernel t : ℂ))) (Ioi 0) := by
    simpa only [mul_neg, Pi.neg_apply] using! (logistic_weight_integrable hs).neg
  have hb : IntegrableOn (fun t : ℝ => (s*(t : ℂ)^(s-1))*_root_.RHTower.salemFermiKernel t) (Ioi 0) := by
    simpa only [mul_assoc] using! (fermi_weight_integrable hs).const_mul s
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun t ht => hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hn)
    (fun t _ => fermi_deriv t) ha hb (boundary_zero hs) (boundary_infty s)
  simp only [mul_neg, integral_neg, sub_self, zero_sub] at hi
  have h := neg_injective hi
  rw [_root_.RHTower.fzzCigarParityMellin_eq_salemFermiMellin, mellin,
    ← integral_const_mul]
  simpa only [smul_eq_mul, mul_assoc] using h

private theorem marked_weight_eq (s : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ)^(s-1)*fzzFermiMarkedDelay t =
      (-3 : ℂ)*((t : ℂ)^s*(_root_.RHTower.logisticKernel t : ℂ)) := by
  have hp : (t : ℂ)^(s-1)*(t : ℂ) = (t : ℂ)^s := by
    simpa only [sub_add_cancel, Complex.cpow_one] using
      (Complex.cpow_add (s-1) 1 (Complex.ofReal_ne_zero.mpr ht.ne')).symm
  rw [fzzFermiMarkedDelay_eq]
  calc
    _ = (-3 : ℂ)*(((t : ℂ)^(s-1)*(t : ℂ))*(_root_.RHTower.logisticKernel t : ℂ)) := by ring
    _ = _ := by rw [hp]

private theorem marked_mellin_convergent {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent fzzFermiMarkedDelay s := by
  change IntegrableOn (fun t : ℝ => (t : ℂ)^(s-1)*fzzFermiMarkedDelay t) (Ioi 0)
  apply ((logistic_weight_integrable hs).const_mul (-3 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (marked_weight_eq s ht).symm

private theorem marked_mellin_eq {s : ℂ} (hs : 0 < s.re) :
    fzzFermiMarkedMellin s = (-3 : ℂ)*s*_root_.RHTower.fzzCigarParityMellin s := by
  rw [fzzFermiMarkedMellin, mellin]
  have h : (∫ t : ℝ in Ioi 0, (t : ℂ)^(s-1) • fzzFermiMarkedDelay t) =
      ∫ t : ℝ in Ioi 0, (-3 : ℂ)*((t : ℂ)^s*(_root_.RHTower.logisticKernel t : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact marked_weight_eq s ht
  rw [h, integral_const_mul, logistic_mellin_identity hs]
  ring

private theorem marked_eventual_eq {s : ℂ} (hs : 0 < s.re) :
    fzzFermiMarkedMellin =ᶠ[𝓝 s] fun z : ℂ => (-3 : ℂ)*z*_root_.RHTower.fzzCigarParityMellin z := by
  have he : {z : ℂ | 0 < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [he] with z hz
  exact marked_mellin_eq hz

private theorem marked_hasDeriv {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt fzzFermiMarkedMellin
      ((-3 : ℂ)*(_root_.RHTower.fzzCigarParityMellin s +
        s*deriv _root_.RHTower.fzzCigarParityMellin s)) s := by
  have hf := (_root_.RHTower.analyticOnNhd_fzzCigarParityMellin s hs).differentiableAt
  have hd : HasDerivAt (fun z : ℂ => (-3 : ℂ)*z*_root_.RHTower.fzzCigarParityMellin z)
      ((-3 : ℂ)*_root_.RHTower.fzzCigarParityMellin s +
        ((-3 : ℂ)*s)*deriv _root_.RHTower.fzzCigarParityMellin s) s := by
    simpa only [id_eq, mul_one] using! (((hasDerivAt_id s).const_mul (-3 : ℂ)).mul hf.hasDerivAt)
  have hc : (-3 : ℂ)*_root_.RHTower.fzzCigarParityMellin s +
      ((-3 : ℂ)*s)*deriv _root_.RHTower.fzzCigarParityMellin s =
      (-3 : ℂ)*(_root_.RHTower.fzzCigarParityMellin s +
        s*deriv _root_.RHTower.fzzCigarParityMellin s) := by ring
  rw [hc] at hd
  exact hd.congr_of_eventuallyEq (marked_eventual_eq hs)

def fzzFermiMarkedMellinPoint (a t : ℝ) : ℂ := (Real.exp a : ℂ)+(t : ℂ)*Complex.I

private theorem point_positive (a t : ℝ) : 0 < (fzzFermiMarkedMellinPoint a t).re := by
  simpa only [fzzFermiMarkedMellinPoint, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero] using Real.exp_pos a

private theorem point_ne_zero (a t : ℝ) : fzzFermiMarkedMellinPoint a t ≠ 0 := by
  intro h
  have hp := point_positive a t
  rw [h, Complex.zero_re] at hp
  exact lt_irrefl _ hp

theorem fzzFermiMarkedMellin_convergent (a t : ℝ) :
    MellinConvergent fzzFermiMarkedDelay (fzzFermiMarkedMellinPoint a t) :=
  marked_mellin_convergent (point_positive a t)

theorem fzzFermiMarkedMellin_eq (a t : ℝ) :
    fzzFermiMarkedMellin (fzzFermiMarkedMellinPoint a t) =
      (-3 : ℂ)*fzzFermiMarkedMellinPoint a t*
        _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) :=
  marked_mellin_eq (point_positive a t)

theorem fzzFermiMarkedMellin_zero_iff (a t : ℝ) :
    fzzFermiMarkedMellin (fzzFermiMarkedMellinPoint a t) = 0 ↔
      _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) = 0 := by
  rw [fzzFermiMarkedMellin_eq]
  exact mul_eq_zero_iff_left (mul_ne_zero (by norm_num : (-3 : ℂ) ≠ 0) (point_ne_zero a t))

theorem hasDerivAt_fzzFermiMarkedMellin (a t : ℝ) :
    HasDerivAt fzzFermiMarkedMellin
      ((-3 : ℂ)*(_root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) +
        fzzFermiMarkedMellinPoint a t*
          deriv _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t)))
      (fzzFermiMarkedMellinPoint a t) := marked_hasDeriv (point_positive a t)

theorem fzzFermiMarkedMellin_deriv (a t : ℝ) :
    deriv fzzFermiMarkedMellin (fzzFermiMarkedMellinPoint a t) =
      (-3 : ℂ)*(_root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) +
        fzzFermiMarkedMellinPoint a t*
          deriv _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t)) :=
  (hasDerivAt_fzzFermiMarkedMellin a t).deriv

theorem fzzFermiMarkedMellin_joint_zero_iff (a t : ℝ) :
    (fzzFermiMarkedMellin (fzzFermiMarkedMellinPoint a t) = 0 ∧
      deriv fzzFermiMarkedMellin (fzzFermiMarkedMellinPoint a t) = 0) ↔
    (_root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) = 0 ∧
      deriv _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) = 0) := by
  rw [fzzFermiMarkedMellin_zero_iff, fzzFermiMarkedMellin_deriv]
  constructor
  · rintro ⟨h0,h1⟩
    refine ⟨h0, ?_⟩
    rw [h0, zero_add] at h1
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (by norm_num))).resolve_left
      (point_ne_zero a t)
  · rintro ⟨h0,h1⟩
    exact ⟨h0, by rw [h0,h1,mul_zero,add_zero,mul_zero]⟩

theorem fzzFermiMarkedMellin_analyticOrder (a t : ℝ) :
    analyticOrderAt fzzFermiMarkedMellin (fzzFermiMarkedMellinPoint a t) =
      analyticOrderAt _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) := by
  let s := fzzFermiMarkedMellinPoint a t
  have hs : 0 < s.re := point_positive a t
  have hu : AnalyticAt ℂ (fun z : ℂ => (-3 : ℂ)*z) s := analyticAt_const.mul analyticAt_id
  have hf := _root_.RHTower.analyticOnNhd_fzzCigarParityMellin s hs
  have hz : analyticOrderAt (fun z : ℂ => (-3 : ℂ)*z) s = 0 :=
    hu.analyticOrderAt_eq_zero.mpr (mul_ne_zero (by norm_num) (point_ne_zero a t))
  rw [analyticOrderAt_congr (marked_eventual_eq hs)]
  change analyticOrderAt ((fun z : ℂ => (-3 : ℂ)*z)*_root_.RHTower.fzzCigarParityMellin) s = _
  rw [analyticOrderAt_mul hu hf, hz, zero_add]

def fzzFermiMarkedMellinStripPoint (a t : ℝ) : ℂ :=
  (((1+Real.exp a)⁻¹ : ℝ) : ℂ)+(t : ℂ)*Complex.I

theorem fzzFermiMarkedMellin_strip_zero_iff_zeta (a t : ℝ) :
    fzzFermiMarkedMellin (fzzFermiMarkedMellinStripPoint a t) = 0 ↔
      riemannZeta (fzzFermiMarkedMellinStripPoint a t) = 0 := by
  have h0 : 0 < (fzzFermiMarkedMellinStripPoint a t).re := by
    simp only [fzzFermiMarkedMellinStripPoint, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  have h1 : (fzzFermiMarkedMellinStripPoint a t).re < 1 := by
    simp only [fzzFermiMarkedMellinStripPoint, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    exact (inv_lt_one₀ (by positivity)).mpr (by linarith [Real.exp_pos a])
  have hn : fzzFermiMarkedMellinStripPoint a t ≠ 0 := by
    intro h; rw [h,Complex.zero_re] at h0; exact lt_irrefl _ h0
  rw [marked_mellin_eq h0, mul_eq_zero_iff_left (mul_ne_zero (by norm_num : (-3 : ℂ) ≠ 0) hn)]
  exact _root_.RHTower.fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero h0 h1

def fzzFermiMarkedLevelDelay (v x : ℝ) : ℂ :=
  ∫ u : ℝ, (fzzExponentialLogCouplingDensity u : ℂ) *
    deriv (fun δ => fzzMarkedRadialReplicaIntegrand u v 0 δ x) 0

def fzzFermiMarkedLevelMellin (v : ℝ) (s : ℂ) : ℂ := mellin (fzzFermiMarkedLevelDelay v) s

private theorem level_radial_zero (u v x : ℝ) :
    fzzMarkedRadialReplicaIntegrand u v 0 0 x = (fzzRadialCouplingDensity u v x : ℂ) := by
  simp [fzzMarkedRadialReplicaIntegrand, fzzRadialCouplingDensity,
    fzzNeutralRadialKernel, fzzNeutralRadialCoordinate, Real.exp_sub, Real.exp_neg,
    div_eq_mul_inv, mul_assoc]

private theorem level_radial_jet (u v x : ℝ) :
    deriv (fun δ => fzzMarkedRadialReplicaIntegrand u v 0 δ x) 0 =
      ((-fzzMarkedRadialReplicaRate v*Real.exp v*x : ℝ) : ℂ)*
        (fzzRadialCouplingDensity u v x : ℂ) := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaIntegrand u v 0 x).deriv, level_radial_zero]
  simp only [neg_mul]

theorem integrable_fzzFermiMarkedLevelDelay_integrand (v x : ℝ) :
    Integrable (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      deriv (fun δ => fzzMarkedRadialReplicaIntegrand u v 0 δ x) 0) := by
  have hi : Integrable (fun u : ℝ =>
      ((-fzzMarkedRadialReplicaRate v*Real.exp v*x : ℝ) : ℂ)*
        ((fzzExponentialLogCouplingDensity u*fzzRadialCouplingDensity u v x : ℝ) : ℂ)) :=
    (integrable_fzzFermiCouplingDensity_integrand v x).ofReal.const_mul _
  apply hi.congr
  filter_upwards with u
  rw [level_radial_jet]
  push_cast
  ring

theorem fzzFermiMarkedLevelDelay_eq (v x : ℝ) :
    fzzFermiMarkedLevelDelay v x =
      ((-fzzMarkedRadialReplicaRate v*Real.exp v*x : ℝ) : ℂ)*
        ((Real.exp v*_root_.RHTower.logisticKernel (Real.exp v*x) : ℝ) : ℂ) := by
  have he : (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      deriv (fun δ => fzzMarkedRadialReplicaIntegrand u v 0 δ x) 0) =
      fun u : ℝ => ((-fzzMarkedRadialReplicaRate v*Real.exp v*x : ℝ) : ℂ)*
        ((fzzExponentialLogCouplingDensity u*fzzRadialCouplingDensity u v x : ℝ) : ℂ) := by
    funext u
    rw [level_radial_jet]
    push_cast
    ring
  rw [fzzFermiMarkedLevelDelay, he, integral_const_mul, integral_complex_ofReal]
  change _*(fzzFermiCouplingDensity v x : ℂ) = _
  rw [fzzFermiCouplingDensity_eq]

theorem fzzFermiMarkedLevelDelay_dilation (v x : ℝ) :
    fzzFermiMarkedLevelDelay v x = ((fzzMarkedRadialReplicaRate v*Real.exp v/3 : ℝ) : ℂ)*
      fzzFermiMarkedDelay (Real.exp v*x) := by
  rw [fzzFermiMarkedLevelDelay_eq, fzzFermiMarkedDelay_eq]
  push_cast
  ring

def fzzFermiMarkedLevelMultiplier (v : ℝ) (s : ℂ) : ℂ :=
  ((fzzMarkedRadialReplicaRate v*Real.exp v/3 : ℝ) : ℂ)*Complex.exp (-(v : ℂ)*s)

theorem fzzFermiMarkedLevelMultiplier_ne_zero (v : ℝ) (s : ℂ) :
    fzzFermiMarkedLevelMultiplier v s ≠ 0 := by
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  apply Complex.ofReal_ne_zero.mpr
  exact (div_pos (mul_pos (fzzMarkedRadialReplicaRate_pos v) (Real.exp_pos v))
    (by norm_num)).ne'

theorem fzzFermiMarkedLevelMellin_dilation (v : ℝ) (s : ℂ) :
    fzzFermiMarkedLevelMellin v s = fzzFermiMarkedLevelMultiplier v s*fzzFermiMarkedMellin s := by
  have he : fzzFermiMarkedLevelDelay v = fun x : ℝ =>
      ((fzzMarkedRadialReplicaRate v*Real.exp v/3 : ℝ) : ℂ) • fzzFermiMarkedDelay (Real.exp v*x) := by
    funext x
    exact fzzFermiMarkedLevelDelay_dilation v x
  rw [fzzFermiMarkedLevelMellin, he, mellin_const_smul,
    mellin_comp_mul_left _ _ (Real.exp_pos v), GaloisForLFunctions.cpow_ofReal_exp]
  simp only [fzzFermiMarkedLevelMultiplier, fzzFermiMarkedMellin, smul_eq_mul,
    mul_neg, neg_mul, mul_assoc]

theorem fzzFermiMarkedLevelMellin_convergent (v a t : ℝ) :
    MellinConvergent (fzzFermiMarkedLevelDelay v) (fzzFermiMarkedMellinPoint a t) := by
  have he : fzzFermiMarkedLevelDelay v = fun x : ℝ =>
      ((fzzMarkedRadialReplicaRate v*Real.exp v/3 : ℝ) : ℂ) • fzzFermiMarkedDelay (Real.exp v*x) := by
    funext x
    exact fzzFermiMarkedLevelDelay_dilation v x
  rw [he]
  exact ((MellinConvergent.comp_mul_left (Real.exp_pos v)).mpr
    (fzzFermiMarkedMellin_convergent a t)).const_smul _

theorem fzzFermiMarkedLevelMellin_eq (v a t : ℝ) :
    fzzFermiMarkedLevelMellin v (fzzFermiMarkedMellinPoint a t) =
      -((fzzMarkedRadialReplicaRate v*Real.exp v : ℝ) : ℂ)*
        Complex.exp (-(v : ℂ)*fzzFermiMarkedMellinPoint a t)*fzzFermiMarkedMellinPoint a t*
          _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) := by
  rw [fzzFermiMarkedLevelMellin_dilation, fzzFermiMarkedMellin_eq, fzzFermiMarkedLevelMultiplier]
  push_cast
  ring

theorem fzzFermiMarkedLevelMellin_zero_iff (v a t : ℝ) :
    fzzFermiMarkedLevelMellin v (fzzFermiMarkedMellinPoint a t) = 0 ↔
      _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) = 0 := by
  rw [fzzFermiMarkedLevelMellin_dilation,
    mul_eq_zero_iff_left (fzzFermiMarkedLevelMultiplier_ne_zero v _), fzzFermiMarkedMellin_zero_iff]

private theorem level_multiplier_deriv (v : ℝ) (s : ℂ) :
    HasDerivAt (fzzFermiMarkedLevelMultiplier v)
      (-(v : ℂ)*fzzFermiMarkedLevelMultiplier v s) s := by
  have h := (((hasDerivAt_id s).const_mul (-(v : ℂ))).cexp).const_mul
    ((fzzMarkedRadialReplicaRate v*Real.exp v/3 : ℝ) : ℂ)
  unfold fzzFermiMarkedLevelMultiplier
  simpa only [id_eq, mul_one, mul_comm, mul_left_comm,
    mul_assoc] using! h

private theorem level_multiplier_analytic (v : ℝ) (s : ℂ) :
    AnalyticAt ℂ (fzzFermiMarkedLevelMultiplier v) s := by
  exact analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp)

theorem hasDerivAt_fzzFermiMarkedLevelMellin (v a t : ℝ) :
    HasDerivAt (fzzFermiMarkedLevelMellin v)
      (fzzFermiMarkedLevelMultiplier v (fzzFermiMarkedMellinPoint a t)*
        (deriv fzzFermiMarkedMellin (fzzFermiMarkedMellinPoint a t) -
          (v : ℂ)*fzzFermiMarkedMellin (fzzFermiMarkedMellinPoint a t)))
      (fzzFermiMarkedMellinPoint a t) := by
  let s := fzzFermiMarkedMellinPoint a t
  have hd := (level_multiplier_deriv v s).mul
    (hasDerivAt_fzzFermiMarkedMellin a t).differentiableAt.hasDerivAt
  have hc : (-(v : ℂ)*fzzFermiMarkedLevelMultiplier v s)*fzzFermiMarkedMellin s +
      fzzFermiMarkedLevelMultiplier v s*deriv fzzFermiMarkedMellin s =
      fzzFermiMarkedLevelMultiplier v s*(deriv fzzFermiMarkedMellin s -
        (v : ℂ)*fzzFermiMarkedMellin s) := by ring
  rw [hc] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall (fzzFermiMarkedLevelMellin_dilation v))

theorem fzzFermiMarkedLevelMellin_joint_zero_iff (v a t : ℝ) :
    (fzzFermiMarkedLevelMellin v (fzzFermiMarkedMellinPoint a t) = 0 ∧
      deriv (fzzFermiMarkedLevelMellin v) (fzzFermiMarkedMellinPoint a t) = 0) ↔
    (_root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) = 0 ∧
      deriv _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) = 0) := by
  rw [← fzzFermiMarkedMellin_joint_zero_iff a t, fzzFermiMarkedLevelMellin_dilation,
    (hasDerivAt_fzzFermiMarkedLevelMellin v a t).deriv,
    mul_eq_zero_iff_left (fzzFermiMarkedLevelMultiplier_ne_zero v _),
    mul_eq_zero_iff_left (fzzFermiMarkedLevelMultiplier_ne_zero v _)]
  constructor <;> rintro ⟨h0,h1⟩ <;> refine ⟨h0, ?_⟩
  · simpa only [h0,mul_zero,sub_zero] using h1
  · simp only [h0,h1,mul_zero,sub_zero]

theorem fzzFermiMarkedLevelMellin_analyticOrder (v a t : ℝ) :
    analyticOrderAt (fzzFermiMarkedLevelMellin v) (fzzFermiMarkedMellinPoint a t) =
      analyticOrderAt _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) := by
  let s := fzzFermiMarkedMellinPoint a t
  have hu := level_multiplier_analytic v s
  have hf : AnalyticAt ℂ fzzFermiMarkedMellin s :=
    ((analyticAt_const.mul analyticAt_id).mul
      (_root_.RHTower.analyticOnNhd_fzzCigarParityMellin s (point_positive a t))).congr
        (marked_eventual_eq (point_positive a t)).symm
  rw [analyticOrderAt_congr (Eventually.of_forall (fzzFermiMarkedLevelMellin_dilation v))]
  change analyticOrderAt (fzzFermiMarkedLevelMultiplier v*fzzFermiMarkedMellin) s = _
  rw [analyticOrderAt_mul hu hf, hu.analyticOrderAt_eq_zero.mpr
    (fzzFermiMarkedLevelMultiplier_ne_zero v s), zero_add]
  exact fzzFermiMarkedMellin_analyticOrder a t

theorem fzzFermiMarkedLevelMellin_strip_zero_iff_zeta (v a t : ℝ) :
    fzzFermiMarkedLevelMellin v (fzzFermiMarkedMellinStripPoint a t) = 0 ↔
      riemannZeta (fzzFermiMarkedMellinStripPoint a t) = 0 := by
  rw [fzzFermiMarkedLevelMellin_dilation,
    mul_eq_zero_iff_left (fzzFermiMarkedLevelMultiplier_ne_zero v _),
    fzzFermiMarkedMellin_strip_zero_iff_zeta]

private def scaledLogistic (v x : ℝ) : ℂ := (_root_.RHTower.logisticKernel (Real.exp v*x) : ℂ)

private theorem scaled_logistic_continuous (v : ℝ) : Continuous (scaledLogistic v) :=
  (Complex.continuous_ofReal.comp _root_.RHTower.continuous_logisticKernel).comp
    (continuous_const.mul continuous_id)

private theorem level_delay_factor (v x : ℝ) :
    fzzFermiMarkedLevelDelay v x = -((fzzMarkedRadialReplicaRate v*Real.exp v^2 : ℝ) : ℂ)*
      (x : ℂ)*scaledLogistic v x := by
  rw [fzzFermiMarkedLevelDelay_eq]
  unfold scaledLogistic
  push_cast
  ring

private theorem level_delay_continuous (v : ℝ) : Continuous (fzzFermiMarkedLevelDelay v) := by
  have he : fzzFermiMarkedLevelDelay v = fun x : ℝ =>
      -((fzzMarkedRadialReplicaRate v*Real.exp v^2 : ℝ) : ℂ)*(x : ℂ)*scaledLogistic v x :=
    funext (level_delay_factor v)
  rw [he]
  exact (continuous_const.mul Complex.continuous_ofReal).mul (scaled_logistic_continuous v)

private theorem scaled_logistic_exp (v : ℝ) :
    scaledLogistic v =O[atTop] (fun x : ℝ => Real.exp (-Real.exp v*x)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Eventually.of_forall (fun x => ?_)⟩
  simp only [scaledLogistic, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (_root_.RHTower.logisticKernel_pos _), abs_of_pos (Real.exp_pos _), one_mul]
  simpa only [neg_mul] using logistic_exp_bound (Real.exp v*x)

private theorem level_delay_top (v a : ℝ) :
    fzzFermiMarkedLevelDelay v =O[atTop] (fun x : ℝ => x^(-a)) := by
  have hx : (fun x : ℝ => (x : ℂ)) =O[atTop] (fun x : ℝ => x) := by
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, Eventually.of_forall (fun x => by simp only [Complex.norm_real, one_mul, le_refl])⟩
  have hg : scaledLogistic v =O[atTop] (fun x : ℝ => x^(-(a+1))) :=
    (scaled_logistic_exp v).trans (isLittleO_exp_neg_mul_rpow_atTop (Real.exp_pos v) _).isBigO
  apply ((hx.mul hg).const_mul_left (-((fzzMarkedRadialReplicaRate v*Real.exp v^2 : ℝ) : ℂ))).congr'
  · filter_upwards with x
    rw [level_delay_factor]
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    calc
      x*x^(-(a+1)) = x^(1 : ℝ)*x^(-(a+1)) := by rw [Real.rpow_one]
      _ = x^((1 : ℝ)+(-(a+1))) := (Real.rpow_add hx _ _).symm
      _ = x^(-a) := by congr 1; ring

private theorem level_delay_bot (v : ℝ) :
    fzzFermiMarkedLevelDelay v =O[𝓝[>] 0] (fun x : ℝ => x^(-(0 : ℝ))) := by
  have h : fzzFermiMarkedLevelDelay v =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
    (((level_delay_continuous v).tendsto 0).mono_left inf_le_left).isBigO_one ℝ
  simpa only [neg_zero, Real.rpow_zero] using h

private theorem level_mellin_differentiation (v : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => Real.log x • fzzFermiMarkedLevelDelay v x) s ∧
      HasDerivAt (fzzFermiMarkedLevelMellin v)
        (mellin (fun x : ℝ => Real.log x • fzzFermiMarkedLevelDelay v x) s) s := by
  exact mellin_hasDerivAt_of_isBigO_rpow
    ((level_delay_continuous v).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (level_delay_top v (s.re+1)) (lt_add_one _) (level_delay_bot v) hs

/-- The mixed insertion is the Mellin integral of the original marked source times log delay. -/
def fzzFermiMarkedLevelMixedMellin (v : ℝ) (s : ℂ) : ℂ :=
  mellin (fun x : ℝ => Real.log x • fzzFermiMarkedLevelDelay v x) s

theorem fzzFermiMarkedLevelMixedMellin_convergent (v a t : ℝ) :
    MellinConvergent (fun x : ℝ => Real.log x • fzzFermiMarkedLevelDelay v x)
      (fzzFermiMarkedMellinPoint a t) :=
  (level_mellin_differentiation v (point_positive a t)).1

theorem fzzFermiMarkedLevelMellin_deriv_eq_integral (v a t : ℝ) :
    deriv (fzzFermiMarkedLevelMellin v) (fzzFermiMarkedMellinPoint a t) =
      fzzFermiMarkedLevelMixedMellin v (fzzFermiMarkedMellinPoint a t) :=
  (level_mellin_differentiation v (point_positive a t)).2.deriv

theorem fzzFermiMarkedLevelMixedMellin_eq (v a t : ℝ) :
    fzzFermiMarkedLevelMixedMellin v (fzzFermiMarkedMellinPoint a t) =
      -((fzzMarkedRadialReplicaRate v*Real.exp v : ℝ) : ℂ)*
        Complex.exp (-(v : ℂ)*fzzFermiMarkedMellinPoint a t)*
          ((1-(v : ℂ)*fzzFermiMarkedMellinPoint a t)*
            _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) +
              fzzFermiMarkedMellinPoint a t*
                deriv _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t)) := by
  rw [← fzzFermiMarkedLevelMellin_deriv_eq_integral,
    (hasDerivAt_fzzFermiMarkedLevelMellin v a t).deriv,
    fzzFermiMarkedMellin_deriv, fzzFermiMarkedMellin_eq, fzzFermiMarkedLevelMultiplier]
  push_cast
  ring

theorem fzzFermiMarkedLevel_integrated_joint_zero_iff (v a t : ℝ) :
    (fzzFermiMarkedLevelMellin v (fzzFermiMarkedMellinPoint a t) = 0 ∧
      fzzFermiMarkedLevelMixedMellin v (fzzFermiMarkedMellinPoint a t) = 0) ↔
    (_root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) = 0 ∧
      deriv _root_.RHTower.fzzCigarParityMellin (fzzFermiMarkedMellinPoint a t) = 0) := by
  rw [← fzzFermiMarkedLevelMellin_deriv_eq_integral]
  exact fzzFermiMarkedLevelMellin_joint_zero_iff v a t

end
end GaloisForLFunctions.RHTower
