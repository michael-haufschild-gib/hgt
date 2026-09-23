import GaloisForLFunctions.RHTower.ProlateUnconditionalChannelBound
import GaloisForLFunctions.RHTower.ProlateCommutationKernel

/-!
# The finite Fourier transform preserves the prolate eigenline

The finite Fourier transform on the aperture, with kernel `exp(i c x t)`, commutes with the prolate
Sturm--Liouville action: the prolate operator acts identically on the two variables of the kernel,
and the weight `1 - t²` vanishes at both endpoints, so the `t`-derivatives move onto the amplitude
with no boundary term.

Consequently the real channel of the finite Fourier transform of a real prolate eigenfunction is
again a prolate eigenfunction with the same separation value.  Since the even prolate eigenline of a
live band eigenvalue is one dimensional, the transform acts on it as a scalar: every such mode is a
finite-Fourier eigenfunction.
-/

noncomputable section

open MeasureTheory

namespace RHTower

/-- The finite Fourier transform of a profile over the aperture. -/
def fourierBandTransform (c : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, bandKernel c x t * f t

/-- The real channel of the finite Fourier transform of a real profile. -/
def realFourierBandTransform (c : ℝ) (Φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (fourierBandTransform c (fun t => ((Φ t : ℝ) : ℂ)) x).re

variable {c : ℝ} {Φ : ℝ → ℝ}

theorem intervalIntegrable_ofReal (hΦ : Continuous Φ) :
    IntervalIntegrable (fun t => ((Φ t : ℝ) : ℂ)) volume (-1) 1 :=
  (Complex.continuous_ofReal.comp hΦ).intervalIntegrable _ _

theorem hasDerivAt_realFourierBandTransform (hΦ : Continuous Φ) (x : ℝ) :
    HasDerivAt (realFourierBandTransform c Φ)
      ((∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) *
        ((Φ t : ℝ) : ℂ)).re) x := by
  have h := hasDerivAt_bandKernelTransform (c := c) (intervalIntegrable_ofReal hΦ) x
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

theorem deriv_realFourierBandTransform (hΦ : Continuous Φ) :
    deriv (realFourierBandTransform c Φ)
      = fun x => (∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) *
          ((Φ t : ℝ) : ℂ)).re :=
  funext fun x => (hasDerivAt_realFourierBandTransform hΦ x).deriv

theorem hasDerivAt_deriv_realFourierBandTransform (hΦ : Continuous Φ) (x : ℝ) :
    HasDerivAt (deriv (realFourierBandTransform c Φ))
      ((∫ t in (-1 : ℝ)..1, bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ (2 : ℕ)) *
        ((Φ t : ℝ) : ℂ)).re) x := by
  rw [deriv_realFourierBandTransform hΦ]
  have h := hasDerivAt_bandTransformDeriv (c := c) (intervalIntegrable_ofReal hΦ) x
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

theorem deriv2_realFourierBandTransform (hΦ : Continuous Φ) :
    deriv (deriv (realFourierBandTransform c Φ))
      = fun x => (∫ t in (-1 : ℝ)..1, bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ (2 : ℕ)) *
          ((Φ t : ℝ) : ℂ)).re :=
  funext fun x => (hasDerivAt_deriv_realFourierBandTransform hΦ x).deriv

/-- **The finite Fourier transform preserves the prolate eigen-equation.** -/
theorem prolateSLAction_realFourierBandTransform {eta : ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x : ℝ, prolateSLAction c Φ x = eta * Φ x) (x : ℝ) :
    prolateSLAction c (realFourierBandTransform c Φ) x
      = eta * realFourierBandTransform c Φ x := by
  have hΦc : Continuous Φ := hsm.continuous
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hdsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Φ) := (contDiff_infty_iff_deriv.mp hsm).2
  have hd2 : Differentiable ℝ (deriv Φ) := (contDiff_infty_iff_deriv.mp hdsm).1
  have hd2c : Continuous (deriv (deriv Φ)) := (contDiff_infty_iff_deriv.mp hdsm).2.continuous
  set f : ℝ → ℂ := fun t => ((Φ t : ℝ) : ℂ) with hf
  set Df : ℝ → ℂ := fun t => ((deriv Φ t : ℝ) : ℂ) with hDf
  set DDf : ℝ → ℂ := fun t => ((deriv (deriv Φ) t : ℝ) : ℂ) with hDDf
  have hfi : IntervalIntegrable f volume (-1) 1 := intervalIntegrable_ofReal hΦc
  have hfd : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt f (Df y) y := by
    intro y _
    exact (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt y (hd1 y).hasDerivAt
  have hfd2 : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt Df (DDf y) y := by
    intro y _
    exact (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt y (hd2 y).hasDerivAt
  have hactionC : ∀ t : ℝ, prolateActionC c f Df DDf t = ((eta * Φ t : ℝ) : ℂ) := by
    intro t
    rw [prolateActionC, hf, hDf, hDDf, ← heig t, prolateSLAction]
    push_cast
    ring
  have hleft : IntervalIntegrable
      (fun t : ℝ => prolateActionC c (fun s => bandKernel c x s)
          (fun s => bandKernel c x s * (Complex.I * ((c * x : ℝ) : ℂ)))
          (fun s => bandKernel c x s * (-(((c * x : ℝ) : ℂ)) ^ (2 : ℕ))) t * f t)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold prolateActionC bandKernel
    fun_prop
  have hright : IntervalIntegrable
      (fun t : ℝ => bandKernel c x t * prolateActionC c f Df DDf t) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    refine Continuous.mul (continuous_bandKernel_snd c x) ?_
    refine (continuous_congr hactionC).mpr ?_
    exact Complex.continuous_ofReal.comp (continuous_const.mul hΦc)
  have hcomm := prolateAction_bandTransform_commutes (c := c) (f := f) (Df := Df) (DDf := DDf)
    x hfi hfd hfd2 hleft hright
  have hrhs : (∫ t in (-1 : ℝ)..1, bandKernel c x t * prolateActionC c f Df DDf t)
      = ((eta : ℝ) : ℂ) * fourierBandTransform c f x := by
    rw [fourierBandTransform, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hactionC t]
    push_cast
    ring
  rw [hrhs] at hcomm
  have hcast1 : (1 - ((x : ℝ) : ℂ) ^ (2 : ℕ)) = (((1 - x ^ (2 : ℕ) : ℝ)) : ℂ) := by push_cast; ring
  have hcast2 : (2 : ℂ) * ((x : ℝ) : ℂ) = (((2 * x : ℝ)) : ℂ) := by push_cast; ring
  have hcast3 : ((c : ℝ) : ℂ) ^ (2 : ℕ) * ((x : ℝ) : ℂ) ^ (2 : ℕ) = (((c ^ (2 : ℕ) * x ^ (2 : ℕ) : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hcast1, hcast2, hcast3] at hcomm
  have hre := congrArg Complex.re hcomm
  simp only [Complex.sub_re, Complex.re_ofReal_mul, hf, fourierBandTransform] at hre
  rw [prolateSLAction, deriv2_realFourierBandTransform hΦc, deriv_realFourierBandTransform hΦc,
    realFourierBandTransform, fourierBandTransform]
  linarith [hre]

/-- The finite Fourier transform preserves evenness. -/
theorem even_fourierBandTransform (heven : Function.Even Φ) (x : ℝ) :
    fourierBandTransform c (fun t => ((Φ t : ℝ) : ℂ)) (-x)
      = fourierBandTransform c (fun t => ((Φ t : ℝ) : ℂ)) x := by
  have hneg := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun t : ℝ => bandKernel c x t * ((Φ t : ℝ) : ℂ))
  rw [neg_neg] at hneg
  rw [fourierBandTransform, fourierBandTransform, ← hneg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  show bandKernel c (-x) t * ((Φ t : ℝ) : ℂ)
    = bandKernel c x (-t) * ((Φ (-t) : ℝ) : ℂ)
  rw [heven t]
  congr 1
  unfold bandKernel
  congr 2
  push_cast
  ring

theorem even_realFourierBandTransform (heven : Function.Even Φ) :
    Function.Even (realFourierBandTransform c Φ) := by
  intro x
  rw [realFourierBandTransform, realFourierBandTransform, even_fourierBandTransform heven x]

theorem differentiable_realFourierBandTransform (hΦ : Continuous Φ) :
    Differentiable ℝ (realFourierBandTransform c Φ) :=
  fun x => (hasDerivAt_realFourierBandTransform hΦ x).differentiableAt

theorem differentiable_deriv_realFourierBandTransform (hΦ : Continuous Φ) :
    Differentiable ℝ (deriv (realFourierBandTransform c Φ)) :=
  fun x => (hasDerivAt_deriv_realFourierBandTransform hΦ x).differentiableAt

theorem continuous_realFourierBandTransform (hΦ : Continuous Φ) :
    Continuous (realFourierBandTransform c Φ) :=
  (differentiable_realFourierBandTransform hΦ).continuous

/-- **The finite Fourier transform is a scalar on the even prolate eigenline.** -/
theorem exists_eqOn_Icc_realFourierBandTransform {eta lam : ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (hne : Φ ≠ 0) (heven : Function.Even Φ)
    (hlam : lam ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x)
    (heig : ∀ x : ℝ, prolateSLAction c Φ x = eta * Φ x) :
    ∃ mu : ℝ, Set.EqOn (realFourierBandTransform c Φ) (fun x => mu * Φ x)
      (Set.Icc (-1 : ℝ) 1) := by
  have hΦc : Continuous Φ := hsm.continuous
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  have hΦ0 : Φ 0 ≠ 0 :=
    value_zero_ne_of_even_joint_prolate_band_eigen hsm hne heven hlam hband heig
  set Ψ := realFourierBandTransform c Φ with hΨ
  have hΨeven : Function.Even Ψ := even_realFourierBandTransform heven
  have hΨd1 : Differentiable ℝ Ψ := differentiable_realFourierBandTransform hΦc
  have hΨd2 : Differentiable ℝ (deriv Ψ) := differentiable_deriv_realFourierBandTransform hΦc
  have hΨeig : ∀ x : ℝ, prolateSLAction c Ψ x = eta * Ψ x :=
    prolateSLAction_realFourierBandTransform hsm heig
  set mu : ℝ := Ψ 0 / Φ 0 with hmu
  have hscaled1 : Differentiable ℝ (fun x => mu * Φ x) := by fun_prop
  have hscaledDeriv : deriv (fun x => mu * Φ x) = fun x => mu * deriv Φ x := by
    funext x
    exact deriv_const_mul mu (hd1 x)
  have hscaled2 : Differentiable ℝ (deriv fun x => mu * Φ x) := by
    rw [hscaledDeriv]
    fun_prop
  have hscaledProlate : ∀ x : ℝ,
      prolateSLAction c (fun y => mu * Φ y) x = eta * (mu * Φ x) := by
    intro x
    rw [GaloisForLFunctions.RHTower.prolateSLAction_const_mul mu hd1 hd2 x, heig x]
    ring
  have hvalue : Ψ 0 = mu * Φ 0 := by
    rw [hmu]
    field_simp
  have hderiv : deriv Ψ 0 = deriv (fun x => mu * Φ x) 0 := by
    rw [hscaledDeriv]
    simp [deriv_zero_of_even hΨeven, deriv_zero_of_even heven]
  have hEqIoo : Set.EqOn Ψ (fun x => mu * Φ x) (Set.Ioo (-1 : ℝ) 1) :=
    eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq hΨd1 hΨd2 hscaled1 hscaled2
      hΨeig hscaledProlate hvalue hderiv
  refine ⟨mu, ?_⟩
  have hclosure : Set.Icc (-1 : ℝ) 1 = closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  rw [hclosure]
  exact hEqIoo.closure hΨd1.continuous hscaled1.continuous

/-- On an even profile the finite Fourier transform is real. -/
theorem fourierBandTransform_ofReal_even (hΦ : Continuous Φ) (heven : Function.Even Φ) (x : ℝ) :
    fourierBandTransform c (fun t => ((Φ t : ℝ) : ℂ)) x
      = ((realFourierBandTransform c Φ x : ℝ) : ℂ) := by
  have hint : IntervalIntegrable (fun t : ℝ => bandKernel c x t * ((Φ t : ℝ) : ℂ))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_bandKernel_snd c x).mul (Complex.continuous_ofReal.comp hΦ)
  have himeq : (∫ t in Set.Ioc (-1 : ℝ) 1, bandKernel c x t * ((Φ t : ℝ) : ℂ)).im
      = ∫ t in Set.Ioc (-1 : ℝ) 1, (bandKernel c x t * ((Φ t : ℝ) : ℂ)).im :=
    (ContinuousLinearMap.integral_comp_comm Complex.imCLM hint.1).symm
  have him : (fourierBandTransform c (fun t => ((Φ t : ℝ) : ℂ)) x).im = 0 := by
    rw [fourierBandTransform, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      himeq]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hzero : (∫ t in (-1 : ℝ)..1, Φ t * Real.sin (c * x * t)) = 0 :=
      integral_even_mul_odd_eq_zero hΦ (by fun_prop) heven (fun t => by
        rw [show c * x * -t = -(c * x * t) by ring, Real.sin_neg])
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hzero
    rw [← hzero]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    show (bandKernel c x t * ((Φ t : ℝ) : ℂ)).im = Φ t * Real.sin (c * x * t)
    unfold bandKernel
    rw [show Complex.I * ((c * x * t : ℝ) : ℂ) = ((c * x * t : ℝ) : ℂ) * Complex.I from
      mul_comm _ _, Complex.exp_mul_I]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re, realFourierBandTransform]
  · rw [Complex.ofReal_im, him]

/-- The scaled Fourier character integral over the aperture is the finite Fourier transform. -/
theorem setIntegral_scaledFourierChar_eq_fourierBandTransform {κ : ℝ} {h : ℝ → ℂ}
    (_hh : Continuous h) (hheven : ∀ t : ℝ, h (-t) = h t) (y : ℝ) :
    (∫ t in Set.Icc (-1 : ℝ) 1,
        Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * h t)
      = fourierBandTransform (2 * Real.pi * κ) h y := by
  have hconv : (∫ t in Set.Icc (-1 : ℝ) 1,
        Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * h t)
      = ∫ t in (-1 : ℝ)..1,
        Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * h t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hneg := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun t : ℝ => bandKernel (2 * Real.pi * κ) y t * h t)
  rw [neg_neg] at hneg
  rw [hconv, fourierBandTransform, ← hneg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  show Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * h t
    = bandKernel (2 * Real.pi * κ) y (-t) * h (-t)
  rw [hheven t]
  congr 1
  unfold bandKernel
  congr 1
  push_cast
  ring

/-- **The band transform is the square of the finite Fourier transform.** -/
theorem bandTransform_eq_kappa_mul_sq {κ : ℝ} (hκ : 0 < κ)
    (hΦ : Continuous Φ) (heven : Function.Even Φ) (x : ℝ) :
    bandTransform (2 * Real.pi * κ) Φ x
      = κ * realFourierBandTransform (2 * Real.pi * κ)
          (realFourierBandTransform (2 * Real.pi * κ) Φ) x := by
  have hΦC : Continuous (fun t : ℝ => ((Φ t : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hΦ
  have hΨc : Continuous (realFourierBandTransform (2 * Real.pi * κ) Φ) :=
    continuous_realFourierBandTransform hΦ
  have hΨeven : Function.Even (realFourierBandTransform (2 * Real.pi * κ) Φ) :=
    even_realFourierBandTransform heven
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ => ((Φ t : ℝ) : ℂ))
      (Set.Icc (-1 : ℝ) 1) volume := hΦC.integrableOn_Icc
  have hgeven : ∀ᵐ t ∂(volume : MeasureTheory.Measure ℝ),
      ((Φ (-t) : ℝ) : ℂ) = ((Φ t : ℝ) : ℂ) :=
    Filter.Eventually.of_forall fun t => by rw [heven t]
  have hdouble := double_integral_scaledFourierChar_eq_sincKernel 1 κ x (by norm_num) hgint hgeven
  have hinner : ∀ y : ℝ, (∫ t in Set.Icc (-1 : ℝ) 1,
      Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * ((Φ t : ℝ) : ℂ))
      = ((realFourierBandTransform (2 * Real.pi * κ) Φ y : ℝ) : ℂ) := by
    intro y
    rw [setIntegral_scaledFourierChar_eq_fourierBandTransform
      (h := fun t : ℝ => ((Φ t : ℝ) : ℂ)) hΦC (fun t => by rw [heven t]) y]
    exact fourierBandTransform_ofReal_even hΦ heven y
  have houter : (∫ y in Set.Icc (-1 : ℝ) 1,
      Complex.exp ((-(2 * Real.pi * κ * x * y) : ℝ) * Complex.I) *
        ((realFourierBandTransform (2 * Real.pi * κ) Φ y : ℝ) : ℂ))
      = ((realFourierBandTransform (2 * Real.pi * κ)
          (realFourierBandTransform (2 * Real.pi * κ) Φ) x : ℝ) : ℂ) := by
    rw [setIntegral_scaledFourierChar_eq_fourierBandTransform
      (h := fun t : ℝ => ((realFourierBandTransform (2 * Real.pi * κ) Φ t : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hΨc) (fun t => by rw [hΨeven t]) x]
    exact fourierBandTransform_ofReal_even hΨc hΨeven x
  have hlhs : (∫ y in Set.Icc (-1 : ℝ) 1,
      Complex.exp ((-(2 * Real.pi * κ * x * y) : ℝ) * Complex.I) *
        ∫ t in Set.Icc (-1 : ℝ) 1,
          Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * ((Φ t : ℝ) : ℂ))
      = ((realFourierBandTransform (2 * Real.pi * κ)
          (realFourierBandTransform (2 * Real.pi * κ) Φ) x : ℝ) : ℂ) := by
    rw [← houter]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [hinner y]
  rw [hlhs] at hdouble
  have hband := scaled_sincIntegral_eq_bandIntegral κ x hκ (fun t : ℝ => ((Φ t : ℝ) : ℂ))
  have hsinc : (∫ t in Set.Icc (-1 : ℝ) 1,
      ((sincSmooth (2 * Real.pi * 1) (κ * (x - t)) : ℝ) : ℂ) * ((Φ t : ℝ) : ℂ))
      = ∫ t in Set.Icc (-1 : ℝ) 1,
        ((sincSmooth (2 * Real.pi) (κ * (x - t)) : ℝ) : ℂ) * ((Φ t : ℝ) : ℂ) := by
    norm_num
  rw [hsinc] at hdouble
  rw [← hdouble] at hband
  have hcast : (∫ t in Set.Icc (-1 : ℝ) 1,
      ((sincKernelSmooth (2 * Real.pi * κ) x t : ℝ) : ℂ) * ((Φ t : ℝ) : ℂ))
      = ((bandTransform (2 * Real.pi * κ) Φ x : ℝ) : ℂ) := by
    rw [bandTransform, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← integral_complex_ofReal]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    push_cast
    ring
  rw [hcast] at hband
  have : ((κ * realFourierBandTransform (2 * Real.pi * κ)
      (realFourierBandTransform (2 * Real.pi * κ) Φ) x : ℝ) : ℂ)
      = ((bandTransform (2 * Real.pi * κ) Φ x : ℝ) : ℂ) := by
    push_cast
    exact hband
  exact (Complex.ofReal_injective this).symm

/-- **Every even mode of a live band eigenvalue is a finite-Fourier eigenfunction.** -/
theorem exists_realFourierBandTransform_eigen {eta lam κ : ℝ} (hκ : 0 < κ)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (hne : Φ ≠ 0) (heven : Function.Even Φ)
    (hlam : lam ≠ 0)
    (hband : ∀ x : ℝ, bandTransform (2 * Real.pi * κ) Φ x = lam * Φ x)
    (heig : ∀ x : ℝ, prolateSLAction (2 * Real.pi * κ) Φ x = eta * Φ x) :
    ∃ mu : ℝ, mu ≠ 0 ∧ κ * mu ^ (2 : ℕ) = lam ∧
      ∀ x : ℝ, realFourierBandTransform (2 * Real.pi * κ) Φ x = mu * Φ x := by
  have hΦc : Continuous Φ := hsm.continuous
  have hΦ0 : Φ 0 ≠ 0 :=
    value_zero_ne_of_even_joint_prolate_band_eigen hsm hne heven hlam hband heig
  obtain ⟨mu, hIcc⟩ := exists_eqOn_Icc_realFourierBandTransform hsm hne heven hlam hband heig
  set Ψ := realFourierBandTransform (2 * Real.pi * κ) Φ with hΨ
  -- the transform only sees the aperture, so it is scalar on `Ψ`
  have hTΨ : ∀ x : ℝ, realFourierBandTransform (2 * Real.pi * κ) Ψ x = mu * Ψ x := by
    intro x
    have hcongr : (∫ t in (-1 : ℝ)..1, bandKernel (2 * Real.pi * κ) x t * ((Ψ t : ℝ) : ℂ))
        = ((mu : ℝ) : ℂ) * ∫ t in (-1 : ℝ)..1,
            bandKernel (2 * Real.pi * κ) x t * ((Φ t : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t ht => ?_
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
        rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      show bandKernel (2 * Real.pi * κ) x t * ((Ψ t : ℝ) : ℂ)
        = ((mu : ℝ) : ℂ) * (bandKernel (2 * Real.pi * κ) x t * ((Φ t : ℝ) : ℂ))
      rw [show Ψ t = mu * Φ t from hIcc htIcc]
      push_cast
      ring
    rw [realFourierBandTransform, fourierBandTransform, hcongr, Complex.re_ofReal_mul]
    rfl
  have hkey : ∀ x : ℝ, lam * Φ x = κ * (mu * Ψ x) := by
    intro x
    rw [← hband x, bandTransform_eq_kappa_mul_sq hκ hΦc heven x, ← hΨ, hTΨ x]
  have hmu : mu ≠ 0 := by
    intro hzero
    apply hne
    funext x
    have h := hkey x
    rw [hzero, zero_mul, mul_zero] at h
    simp only [Pi.zero_apply]
    exact (mul_eq_zero.mp h).resolve_left hlam
  have hΨ0 : Ψ 0 = mu * Φ 0 := hIcc (by norm_num)
  have hsq : κ * mu ^ (2 : ℕ) = lam := by
    have h := hkey 0
    rw [hΨ0] at h
    have hcancel : lam * Φ 0 = κ * mu ^ (2 : ℕ) * Φ 0 := by
      rw [h]
      ring
    exact (mul_right_cancel₀ hΦ0 hcancel).symm
  refine ⟨mu, hmu, hsq, fun x => ?_⟩
  have h := hkey x
  rw [← hsq] at h
  have hκmu : κ * mu ≠ 0 := mul_ne_zero hκ.ne' hmu
  have hstep : (κ * mu) * (mu * Φ x) = (κ * mu) * Ψ x := by
    calc (κ * mu) * (mu * Φ x) = κ * mu ^ (2 : ℕ) * Φ x := by ring
      _ = κ * (mu * Ψ x) := h
      _ = (κ * mu) * Ψ x := by ring
  exact (mul_left_cancel₀ hκmu hstep).symm

end RHTower
