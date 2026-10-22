import GaloisForLFunctions.RHTower.Suzuki.SuzukiLiteralPairedSourceAssembly
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOnePrimeRoughPrimitiveFourierForcing
import GaloisForLFunctions.RHTower.VectorL2WeakCutoffProduct

/-!
# Literal interior cutoff for the one-prime terminal pair

At Suzuki's two physical roots, the exterior punctures are killed identically.  The two interior
punctures have the same source-derived cutoff

`χₐ(L) = smoothTransition (2 a exp L - 1)`.

This module identifies both coordinate cutoffs with `χₐ`, proves that `χₐ` has temperate growth and
is essentially bounded, and proves that its derivative is compactly supported in the exact event
interval `[log((2a)⁻¹), log(a⁻¹)]`.  It then instantiates the Hilbert-valued weak Leibniz rule on
the literal two-coordinate terminal source space.  Thus cutoff events are genuine `L²` source
terms rather than formal pointwise symbols.
-/

open Set MeasureTheory Filter
open scoped LineDeriv SchwartzMap

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Common scalar cutoff of the two physical interior punctures. -/
def suzukiOnePrimeInteriorCutoffReal (a L : ℝ) : ℝ :=
  Real.smoothTransition (2 * a * Real.exp L - 1)

/-- Complex scalar cutoff used on the terminal Hilbert source. -/
def suzukiOnePrimeInteriorCutoff (a L : ℝ) : ℂ :=
  (suzukiOnePrimeInteriorCutoffReal a L : ℂ)

/-- Derivative of the common terminal interior cutoff. -/
def suzukiOnePrimeInteriorCutoffDeriv (a L : ℝ) : ℂ :=
  ((deriv (suzukiOnePrimeInteriorCutoffReal a : ℝ → ℝ) L : ℝ) : ℂ)

theorem contDiff_suzukiOnePrimeInteriorCutoffReal (a : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (suzukiOnePrimeInteriorCutoffReal a) := by
  unfold suzukiOnePrimeInteriorCutoffReal
  apply Real.smoothTransition.contDiff.comp
  fun_prop

/-- Outside the exact event interval the cutoff derivative vanishes. -/
theorem deriv_suzukiOnePrimeInteriorCutoffReal_eq_zero_of_not_mem
    {a L : ℝ} (ha : 0 < a)
    (hL : L ∉ Icc (Real.log ((2 * a)⁻¹)) (Real.log (a⁻¹))) :
    deriv (suzukiOnePrimeInteriorCutoffReal a) L = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hL
  rcases hL with hlow | hhigh
  · have hinvpos : 0 < (2 * a)⁻¹ := by positivity
    have hexp : Real.exp L < (2 * a)⁻¹ := by
      rw [← Real.exp_log hinvpos]
      exact Real.exp_lt_exp.mpr hlow
    have hmul := mul_lt_mul_of_pos_left hexp (by positivity : 0 < 2 * a)
    have harg : 2 * a * Real.exp L - 1 < 0 := by
      rw [mul_inv_cancel₀ (by positivity : 2 * a ≠ 0)] at hmul
      linarith
    have harg_cont : Continuous fun y : ℝ => 2 * a * Real.exp y - 1 := by fun_prop
    have hev : ∀ᶠ y in nhds L, 2 * a * Real.exp y - 1 < 0 :=
      harg_cont.continuousAt (Iio_mem_nhds harg)
    have heq : suzukiOnePrimeInteriorCutoffReal a =ᶠ[nhds L] fun _ => 0 := by
      filter_upwards [hev] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.deriv_eq, deriv_const]
  · have hinvpos : 0 < a⁻¹ := by positivity
    have hexp : a⁻¹ < Real.exp L := by
      rw [← Real.exp_log hinvpos]
      exact Real.exp_lt_exp.mpr hhigh
    have hmul := mul_lt_mul_of_pos_left hexp ha
    have harg : 1 < 2 * a * Real.exp L - 1 := by
      rw [mul_inv_cancel₀ ha.ne'] at hmul
      nlinarith [Real.exp_pos L]
    have harg_cont : Continuous fun y : ℝ => 2 * a * Real.exp y - 1 := by fun_prop
    have hev : ∀ᶠ y in nhds L, 1 < 2 * a * Real.exp y - 1 :=
      harg_cont.continuousAt (Ioi_mem_nhds harg)
    have heq : suzukiOnePrimeInteriorCutoffReal a =ᶠ[nhds L] fun _ => 1 := by
      filter_upwards [hev] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.deriv_eq, deriv_const]

theorem hasCompactSupport_deriv_suzukiOnePrimeInteriorCutoffReal
    {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (deriv (suzukiOnePrimeInteriorCutoffReal a)) := by
  refine HasCompactSupport.intro
    (K := Icc (Real.log ((2 * a)⁻¹)) (Real.log (a⁻¹))) isCompact_Icc fun L hL => ?_
  exact deriv_suzukiOnePrimeInteriorCutoffReal_eq_zero_of_not_mem ha hL

theorem hasCompactSupport_fderiv_suzukiOnePrimeInteriorCutoffReal
    {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (fderiv ℝ (suzukiOnePrimeInteriorCutoffReal a)) := by
  refine HasCompactSupport.intro
    (K := Icc (Real.log ((2 * a)⁻¹)) (Real.log (a⁻¹))) isCompact_Icc fun L hL => ?_
  apply ContinuousLinearMap.ext
  intro y
  rw [fderiv_eq_smul_deriv,
    deriv_suzukiOnePrimeInteriorCutoffReal_eq_zero_of_not_mem ha hL, smul_zero]
  rfl

theorem hasTemperateGrowth_suzukiOnePrimeInteriorCutoffReal
    {a : ℝ} (ha : 0 < a) :
    Function.HasTemperateGrowth (suzukiOnePrimeInteriorCutoffReal a) := by
  have hcont := contDiff_suzukiOnePrimeInteriorCutoffReal a
  have hfd_cont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (suzukiOnePrimeInteriorCutoffReal a)) :=
    (contDiff_infty_iff_fderiv.mp hcont).2
  have hfd_temp :=
    (hasCompactSupport_fderiv_suzukiOnePrimeInteriorCutoffReal ha).hasTemperateGrowth hfd_cont
  refine Function.HasTemperateGrowth.of_fderiv hfd_temp
    (contDiff_infty_iff_fderiv.mp hcont).1 (k := 0) (C := 1) ?_
  intro L
  simp only [pow_zero, mul_one, suzukiOnePrimeInteriorCutoffReal, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one (2 * a * Real.exp L - 1)

theorem hasTemperateGrowth_deriv_suzukiOnePrimeInteriorCutoffReal
    {a : ℝ} (ha : 0 < a) :
    Function.HasTemperateGrowth (deriv (suzukiOnePrimeInteriorCutoffReal a)) := by
  exact (hasCompactSupport_deriv_suzukiOnePrimeInteriorCutoffReal ha).hasTemperateGrowth
    (contDiff_infty_iff_deriv.mp (contDiff_suzukiOnePrimeInteriorCutoffReal a)).2

theorem hasTemperateGrowth_suzukiOnePrimeInteriorCutoff
    {a : ℝ} (ha : 0 < a) :
    Function.HasTemperateGrowth (suzukiOnePrimeInteriorCutoff a) := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp
    (hasTemperateGrowth_suzukiOnePrimeInteriorCutoffReal ha)

theorem hasTemperateGrowth_suzukiOnePrimeInteriorCutoffDeriv
    {a : ℝ} (ha : 0 < a) :
    Function.HasTemperateGrowth (suzukiOnePrimeInteriorCutoffDeriv a) := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp
    (hasTemperateGrowth_deriv_suzukiOnePrimeInteriorCutoffReal ha)

theorem hasDerivAt_suzukiOnePrimeInteriorCutoff
    (a L : ℝ) :
    HasDerivAt (suzukiOnePrimeInteriorCutoff a)
      (suzukiOnePrimeInteriorCutoffDeriv a L) L := by
  change HasDerivAt (fun x : ℝ => (suzukiOnePrimeInteriorCutoffReal a x : ℂ))
    ((deriv (suzukiOnePrimeInteriorCutoffReal a : ℝ → ℝ) L : ℝ) : ℂ) L
  have hr : HasDerivAt (suzukiOnePrimeInteriorCutoffReal a)
      (deriv (suzukiOnePrimeInteriorCutoffReal a) L) L :=
    (contDiff_infty_iff_deriv.mp (contDiff_suzukiOnePrimeInteriorCutoffReal a)).1 L |>.hasDerivAt
  have hc := Complex.ofRealCLM.hasDerivAt.scomp L hr
  simpa [Function.comp_def] using hc

theorem memLp_top_suzukiOnePrimeInteriorCutoff (a : ℝ) :
    MemLp (suzukiOnePrimeInteriorCutoff a) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound
    (Complex.ofRealCLM.continuous.comp
      (contDiff_suzukiOnePrimeInteriorCutoffReal a).continuous |>.aestronglyMeasurable) 1 ?_
  filter_upwards with L
  simp only [suzukiOnePrimeInteriorCutoff, suzukiOnePrimeInteriorCutoffReal,
    Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem memLp_top_suzukiOnePrimeInteriorCutoffDeriv
    {a : ℝ} (ha : 0 < a) :
    MemLp (suzukiOnePrimeInteriorCutoffDeriv a) ⊤ (volume : Measure ℝ) := by
  have hcont : Continuous (deriv (suzukiOnePrimeInteriorCutoffReal a)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_suzukiOnePrimeInteriorCutoffReal a)).2.continuous
  obtain ⟨C, hC⟩ :=
    (hasCompactSupport_deriv_suzukiOnePrimeInteriorCutoffReal ha).exists_bound_of_continuous hcont
  refine memLp_top_of_bound
    (Complex.ofRealCLM.continuous.comp hcont |>.aestronglyMeasurable) C ?_
  filter_upwards with L
  simpa [suzukiOnePrimeInteriorCutoffDeriv, Complex.norm_real] using hC L

/-- Right-root interior puncture has the common terminal cutoff. -/
theorem suzukiScaleBufferedCutoff_right_root_interior
    (a L : ℝ) :
    suzukiScaleBufferedCutoff a a (-1) L = suzukiOnePrimeInteriorCutoffReal a L := by
  rw [suzukiScaleBufferedCutoff, suzukiRightScaleBufferArgument_eq,
    suzukiLeftScaleBufferArgument_eq]
  simp [suzukiOnePrimeInteriorCutoffReal]
  ring_nf

/-- Left-root interior puncture has the same common terminal cutoff. -/
theorem suzukiScaleBufferedCutoff_left_root_interior
    (a L : ℝ) :
    suzukiScaleBufferedCutoff a (-a) 1 L = suzukiOnePrimeInteriorCutoffReal a L := by
  rw [suzukiScaleBufferedCutoff, suzukiRightScaleBufferArgument_eq,
    suzukiLeftScaleBufferArgument_eq]
  simp [suzukiOnePrimeInteriorCutoffReal]
  ring_nf

/-- Literal common-cutoff product on the two-coordinate one-prime terminal source. -/
def onePrimeTerminalInteriorCutoffSource
    (a : ℝ) (f : _root_.RHTower.OnePrimeTerminalSourceL2) :
    _root_.RHTower.OnePrimeTerminalSourceL2 :=
  _root_.RHTower.l2CutoffProduct (suzukiOnePrimeInteriorCutoff a)
    (memLp_top_suzukiOnePrimeInteriorCutoff a) f

/-- The two terminal interior cutoff events form an actual `L²` weak source with the exact
Leibniz sign. -/
theorem onePrimeTerminalInteriorCutoffSource_weakDerivative
    {a : ℝ} (ha : 0 < a)
    (G H : _root_.RHTower.OnePrimeTerminalSourceL2)
    (hweak : ∂_{(1 : ℝ)} (G : 𝓢'(ℝ, _root_.RHTower.OnePrimeTerminalState)) =
      (H : 𝓢'(ℝ, _root_.RHTower.OnePrimeTerminalState))) :
    ∂_{(1 : ℝ)}
        (onePrimeTerminalInteriorCutoffSource a G :
          𝓢'(ℝ, _root_.RHTower.OnePrimeTerminalState)) =
      ((onePrimeTerminalInteriorCutoffSource a H +
          _root_.RHTower.l2CutoffProduct (suzukiOnePrimeInteriorCutoffDeriv a)
            (memLp_top_suzukiOnePrimeInteriorCutoffDeriv ha) G :
        _root_.RHTower.OnePrimeTerminalSourceL2) :
          𝓢'(ℝ, _root_.RHTower.OnePrimeTerminalState)) := by
  exact _root_.RHTower.l2CutoffProduct_weakDerivative
    (suzukiOnePrimeInteriorCutoff a) (suzukiOnePrimeInteriorCutoffDeriv a)
    (hasTemperateGrowth_suzukiOnePrimeInteriorCutoff ha)
    (hasTemperateGrowth_suzukiOnePrimeInteriorCutoffDeriv ha)
    (memLp_top_suzukiOnePrimeInteriorCutoff a)
    (memLp_top_suzukiOnePrimeInteriorCutoffDeriv ha)
    (hasDerivAt_suzukiOnePrimeInteriorCutoff a) G H hweak

end GaloisForLFunctions.RHTower

end
