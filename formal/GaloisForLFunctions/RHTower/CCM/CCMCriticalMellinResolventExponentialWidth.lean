import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszResolventRHCriterion
import GaloisForLFunctions.RHTower.CCM.CCMSourceDivisorEnergySpectrum
import GaloisForLFunctions.RHTower.XiSourceMatroidCircuitFracture

/-!
# Exponential-width spectrum for the critical Mellin Chebyshev resolvent

An exponential envelope `|Q(t)| ≤ B exp(alpha t)` for the unit-Riesz critical Mellin
Chebyshev resolvent manufactures analytic continuation only above the translated abscissa
`alpha - 1/2`.  Rotating this continuation into centered Xi coordinates excludes every Xi zero
to the right of `Re rho = 1/2 + alpha`.

This is the quantitative form of the bounded-resolvent RH endpoint.  It records, without an RH
premise, exactly how a lost exponential rate becomes lost zero-free width.
-/

open Complex Filter Function Set MeasureTheory Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def ccmXiUpperHalfPlaneAbove (alpha : ℝ) : Set ℂ :=
  {z : ℂ | alpha < z.im}

theorem isOpen_ccmXiUpperHalfPlaneAbove (alpha : ℝ) :
    IsOpen (ccmXiUpperHalfPlaneAbove alpha) := by
  exact isOpen_lt continuous_const Complex.continuous_im

theorem xiZeroHalfPlaneBound_of_upper_logDeriv_extensionAbove
    {alpha : ℝ}
    (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A (ccmXiUpperHalfPlaneAbove alpha))
    (hagree : ∀ w : ℂ, 1 / 2 < w.im → A w = logDeriv XiC w) :
    XiZeroHalfPlaneBound alpha := by
  have hUopen : IsOpen (ccmXiUpperHalfPlaneAbove alpha) :=
    isOpen_ccmXiUpperHalfPlaneAbove alpha
  have hUpre : IsPreconnected (ccmXiUpperHalfPlaneAbove alpha) := by
    exact (convex_halfSpace_im_gt alpha).isPreconnected
  let H : ℂ → ℂ := fun w => deriv XiC w - A w * XiC w
  have hHan : AnalyticOnNhd ℂ H (ccmXiUpperHalfPlaneAbove alpha) := by
    intro w hw
    exact (XiC_analytic w (Set.mem_univ w)).deriv.sub
      ((hA w hw).mul (XiC_analytic w (Set.mem_univ w)))
  let w₀ : ℂ := (max (alpha + 1) 1 : ℝ) * I
  have hw₀ : w₀ ∈ ccmXiUpperHalfPlaneAbove alpha := by
    change alpha < ((max (alpha + 1) 1 : ℝ) * I).im
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero]
    have hmax : alpha + 1 ≤ max (alpha + 1) 1 := le_max_left _ _
    linarith
  have hw₀high : 1 / 2 < w₀.im := by
    dsimp only [w₀]
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero]
    have hmax : (1 : ℝ) ≤ max (alpha + 1) 1 := le_max_right _ _
    linarith
  have hHev : H =ᶠ[𝓝 w₀] 0 := by
    have hhigh : {w : ℂ | 1 / 2 < w.im} ∈ 𝓝 w₀ := by
      apply (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      exact hw₀high
    filter_upwards [hhigh] with w hw
    have hXi : XiC w ≠ 0 := by
      intro hzero
      have hstrip := xiC_zero_im_mem_openHalf hzero
      linarith
    have hag := hagree w hw
    dsimp only [H]
    rw [hag, logDeriv_apply]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hXi).symm
  have hHzero : EqOn H 0 (ccmXiUpperHalfPlaneAbove alpha) :=
    hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hUpre hw₀ hHev
  have hnozero : ∀ {z : ℂ}, z ∈ ccmXiUpperHalfPlaneAbove alpha → XiC z ≠ 0 := by
    intro z hzU hzero
    have hXiNe : ∀ᶠ w in 𝓝[≠] z, XiC w ≠ 0 :=
      (XiC_analytic z
        (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
          (fun hlocal =>
            XiC_order_ne_top z (analyticOrderAt_eq_top.mpr hlocal))
    have hUevent : ∀ᶠ w in 𝓝[≠] z, w ∈ ccmXiUpperHalfPlaneAbove alpha :=
      Filter.Eventually.filter_mono inf_le_left (hUopen.mem_nhds hzU)
    apply XiC_ne_zero_of_logDeriv_eventuallyEq_analytic (hA z hzU) ?_ hzero
    filter_upwards [hXiNe, hUevent] with w hwXi hwU
    rw [logDeriv_apply]
    apply (div_eq_iff hwXi).2
    exact sub_eq_zero.mp (hHzero hwU)
  intro rho hzero
  by_contra hnot
  have hrho : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
  let zrho : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  let z : ℂ := xiSpectralPointSupport zrho
  have hzZero : XiC z = 0 := by
    exact XiC_xiSpectralPointSupport_eq_zero_sourceCircuit zrho
  have hzIm : z.im = 1 / 2 - rho.re := by
    exact xiSpectralPointSupport_im_eq_half_sub_re zrho
  have hnegMem : -z ∈ ccmXiUpperHalfPlaneAbove alpha := by
    change alpha < (-z).im
    rw [neg_im, hzIm]
    linarith
  have hnegZero : XiC (-z) = 0 := by
    rw [XiC_even, hzZero]
  exact hnozero hnegMem hnegZero

def CriticalMellinChebyshevResolventExponentialBounded (alpha : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
    |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t)

def criticalMellinChebyshevResolventTiltedRay
    (alpha h : ℝ) : ℝ :=
  Real.exp (-alpha * h) *
    criticalMellinChebyshevResolventRayRepresentative (h - 1)

theorem measurable_criticalMellinChebyshevResolventTiltedRay (alpha : ℝ) :
    Measurable (criticalMellinChebyshevResolventTiltedRay alpha) := by
  unfold criticalMellinChebyshevResolventTiltedRay
  have hleft : Measurable (fun h : ℝ => Real.exp (-alpha * h)) := by
    exact Real.measurable_exp.comp
      (measurable_const.mul measurable_id)
  have hright : Measurable (fun h : ℝ =>
      criticalMellinChebyshevResolventRayRepresentative (h - 1)) := by
    exact continuous_criticalMellinChebyshevResolventRayRepresentative.measurable.comp
      (measurable_id.sub measurable_const)
  exact hleft.mul hright

theorem abs_criticalMellinChebyshevResolventTiltedRay_le
    {alpha B h : ℝ}
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hh : 1 < h) :
    |criticalMellinChebyshevResolventTiltedRay alpha h| ≤
      B * Real.exp (-alpha) := by
  have ht : 0 ≤ h - 1 := by linarith
  rw [criticalMellinChebyshevResolventTiltedRay, abs_mul,
    abs_of_pos (Real.exp_pos _),
    criticalMellinChebyshevResolventRayRepresentative_eq ht]
  calc
    Real.exp (-alpha * h) *
        |criticalMellinChebyshevResolventSource (h - 1)| ≤
        Real.exp (-alpha * h) *
          (B * Real.exp (alpha * (h - 1))) := by
      gcongr
      exact hB (h - 1) ht
    _ = B * Real.exp (-alpha) := by
      rw [show Real.exp (-alpha * h) *
          (B * Real.exp (alpha * (h - 1))) =
        B * (Real.exp (-alpha * h) * Real.exp (alpha * (h - 1))) by ring,
        ← Real.exp_add]
      congr 2
      ring

def criticalMellinChebyshevResolventLaplaceExponentialExtension
    (alpha : ℝ) (z : ℂ) : ℂ :=
  Complex.exp z * ccmAbelLaplaceTail
    (criticalMellinChebyshevResolventTiltedRay alpha) 1 (z - alpha)

theorem criticalMellinChebyshevResolventLaplace_eq_exponentialExtension
    (alpha : ℝ) (z : ℂ) :
    criticalMellinChebyshevResolventLaplace z =
      criticalMellinChebyshevResolventLaplaceExponentialExtension alpha z := by
  rw [criticalMellinChebyshevResolventLaplace_eq_shiftedTail]
  unfold criticalMellinChebyshevResolventLaplaceExponentialExtension
  congr 1
  rw [ccmAbelLaplaceTail, ccmAbelLaplaceTail]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h hh
  unfold criticalMellinChebyshevResolventTiltedRay
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem analyticOnNhd_criticalMellinChebyshevResolventLaplace_of_exponentialBound
    {alpha B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t)) :
    AnalyticOnNhd ℂ criticalMellinChebyshevResolventLaplace
      {z : ℂ | alpha < z.re} := by
  have hC0 : 0 ≤ B * Real.exp (-alpha) :=
    mul_nonneg hB0 (Real.exp_pos _).le
  have htail := analyticOnNhd_ccmAbelLaplaceTail_of_bounded
    (measurable_criticalMellinChebyshevResolventTiltedRay alpha)
    (show (0 : ℝ) < 1 by norm_num) hC0
    (fun h hh => abs_criticalMellinChebyshevResolventTiltedRay_le hB hh)
  rw [show criticalMellinChebyshevResolventLaplace =
      criticalMellinChebyshevResolventLaplaceExponentialExtension alpha by
    funext z
    exact criticalMellinChebyshevResolventLaplace_eq_exponentialExtension alpha z]
  intro z hz
  have hshift : AnalyticAt ℂ (fun w : ℂ => w - (alpha : ℂ)) z := by
    fun_prop
  have hzshift : 0 < (z - (alpha : ℂ)).re := by
    norm_num [Complex.sub_re] at hz ⊢
    linarith
  have hcomp : AnalyticAt ℂ
      (fun w : ℂ => ccmAbelLaplaceTail
        (criticalMellinChebyshevResolventTiltedRay alpha) 1
        (w - (alpha : ℂ))) z :=
    AnalyticAt.comp (f := fun w : ℂ => w - (alpha : ℂ))
      (htail (z - (alpha : ℂ)) hzshift) hshift
  unfold criticalMellinChebyshevResolventLaplaceExponentialExtension
  exact analyticAt_id.cexp.mul hcomp

theorem abs_unitRieszChebyshevRayIntegral_le_of_resolvent_exponentialBound
    {alpha B : ℝ}
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    {t : ℝ} (ht : 0 ≤ t) :
    |unitRieszChebyshevRayIntegral t| ≤
      Real.exp t * (B * Real.exp (alpha * t)) + 2 / 3 := by
  rw [unitRieszChebyshevRayIntegral_eq_fullResolvent ht]
  calc
    |Real.exp t * criticalMellinChebyshevResolventSource t + 2 / 3| ≤
        |Real.exp t * criticalMellinChebyshevResolventSource t| + |2 / 3| :=
      abs_add_le _ _
    _ = Real.exp t * |criticalMellinChebyshevResolventSource t| + 2 / 3 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos t)]
      norm_num
    _ ≤ Real.exp t * (B * Real.exp (alpha * t)) + 2 / 3 := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left (hB t ht) (Real.exp_pos t).le) _

theorem integrableOn_exp_mul_unitRieszChebyshevRayIntegral_of_exponentialBound
    {alpha B r : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hrNegOne : -1 < r)
    (hr : alpha < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-(r + 1) * t) *
      unitRieszChebyshevRayIntegral t) (Ioi 0) := by
  let M : ℝ → ℝ := fun t =>
    B * Real.exp ((alpha - r) * t) +
      (2 / 3) * Real.exp (-(r + 1) * t)
  have hrOne : 0 < r + 1 := by linarith
  have hfirst : IntegrableOn
      (fun t : ℝ => B * Real.exp ((alpha - r) * t)) (Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (show alpha - r < 0 by linarith) 0).const_mul B
  have hsecond : IntegrableOn
      (fun t : ℝ => (2 / 3) * Real.exp (-(r + 1) * t)) (Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (show -(r + 1) < 0 by linarith) 0).const_mul (2 / 3)
  have hmajor : IntegrableOn M (Ioi 0) := hfirst.add hsecond
  refine hmajor.mono'
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      continuous_unitRieszChebyshevRayIntegral.measurable).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ht.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(r + 1) * t) * |unitRieszChebyshevRayIntegral t| ≤
        Real.exp (-(r + 1) * t) *
          (Real.exp t * (B * Real.exp (alpha * t)) + 2 / 3) := by
      gcongr
      exact abs_unitRieszChebyshevRayIntegral_le_of_resolvent_exponentialBound hB ht0
    _ = M t := by
      dsimp only [M]
      rw [mul_add]
      rw [show Real.exp (-(r + 1) * t) *
          (Real.exp t * (B * Real.exp (alpha * t))) =
        B * Real.exp ((alpha - r) * t) by
        rw [show Real.exp (-(r + 1) * t) *
            (Real.exp t * (B * Real.exp (alpha * t))) =
          B * (Real.exp (-(r + 1) * t) * Real.exp t *
            Real.exp (alpha * t)) by ring,
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring]
      ring

theorem tendsto_exp_mul_unitRieszChebyshevRayIntegral_atTop_of_exponentialBound
    {alpha B r : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hrNegOne : -1 < r)
    (hr : alpha < r) :
    Tendsto (fun t : ℝ => Real.exp (-(r + 1) * t) *
      unitRieszChebyshevRayIntegral t) atTop (nhds 0) := by
  have hrOne : 0 < r + 1 := by linarith
  have hdecayR : Tendsto (fun t : ℝ => Real.exp ((alpha - r) * t))
      atTop (nhds 0) := by
    have hlinear : Tendsto (fun t : ℝ => (alpha - r) * t) atTop atBot := by
      simpa only [id_eq, show alpha - r = -(r - alpha) by ring] using
        (tendsto_const_nhds.neg_mul_atTop
          (show -(r - alpha) < 0 by linarith) tendsto_id)
    exact Real.tendsto_exp_atBot.comp hlinear
  have hdecayA : Tendsto (fun t : ℝ => Real.exp (-(r + 1) * t))
      atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (show -(r + 1) < 0 by linarith) tendsto_id)
  have hmajor : Tendsto (fun t : ℝ =>
      B * Real.exp ((alpha - r) * t) +
        (2 / 3) * Real.exp (-(r + 1) * t)) atTop (nhds 0) := by
    simpa using (hdecayR.const_mul B).add (hdecayA.const_mul (2 / 3))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(r + 1) * t) * |unitRieszChebyshevRayIntegral t| ≤
        Real.exp (-(r + 1) * t) *
          (Real.exp t * (B * Real.exp (alpha * t)) + 2 / 3) := by
      gcongr
      exact abs_unitRieszChebyshevRayIntegral_le_of_resolvent_exponentialBound hB ht
    _ = B * Real.exp ((alpha - r) * t) +
        (2 / 3) * Real.exp (-(r + 1) * t) := by
      rw [mul_add]
      rw [show Real.exp (-(r + 1) * t) *
          (Real.exp t * (B * Real.exp (alpha * t))) =
        B * Real.exp ((alpha - r) * t) by
        rw [show Real.exp (-(r + 1) * t) *
            (Real.exp t * (B * Real.exp (alpha * t))) =
          B * (Real.exp (-(r + 1) * t) * Real.exp t *
            Real.exp (alpha * t)) by ring,
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring]
      ring

theorem integral_Ioi_exp_mul_criticalMellinChebyshevRayDensity_eq_of_exponentialBound
    {alpha B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hrHalf : 1 / 2 < r) (hrAlpha : alpha < r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(r + 1) * t) *
      criticalMellinChebyshevRayDensity t) =
      (r + 1) * (∫ t in Ioi (0 : ℝ),
        Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t) := by
  have hrNegOne : -1 < r := by linarith
  have hleft := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ)
    (integrableOn_exp_mul_criticalMellinChebyshevRayDensity hrHalf) tendsto_id
  have hright0 := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ)
    (integrableOn_exp_mul_unitRieszChebyshevRayIntegral_of_exponentialBound
      hB0 hB hrNegOne hrAlpha) tendsto_id
  have hright : Tendsto (fun T : ℝ =>
      Real.exp (-(r + 1) * T) * unitRieszChebyshevRayIntegral T +
        (r + 1) * (∫ t in (0 : ℝ)..T,
          Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t))
      atTop (nhds ((r + 1) * (∫ t in Ioi (0 : ℝ),
        Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t))) := by
    have hterminal :=
      tendsto_exp_mul_unitRieszChebyshevRayIntegral_atTop_of_exponentialBound
        hB0 hB hrNegOne hrAlpha
    simpa only [id_eq, zero_add] using hterminal.add (hright0.const_mul (r + 1))
  have heq : (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      Real.exp (-(r + 1) * t) * criticalMellinChebyshevRayDensity t) =ᶠ[atTop]
      (fun T : ℝ =>
        Real.exp (-(r + 1) * T) * unitRieszChebyshevRayIntegral T +
          (r + 1) * (∫ t in (0 : ℝ)..T,
            Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact intervalIntegral_exp_mul_criticalMellinChebyshevRayDensity_eq hT
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

theorem integrableOn_exp_mul_criticalMellinChebyshevResolventRayRepresentative_of_exponentialBound
    {alpha B r : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hr : alpha < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-r * t) *
      criticalMellinChebyshevResolventRayRepresentative t) (Ioi 0) := by
  have hmajor : IntegrableOn
      (fun t : ℝ => B * Real.exp ((alpha - r) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show alpha - r < 0 by linarith) 0).const_mul B
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-r * t) *
      criticalMellinChebyshevResolventRayRepresentative t)
      (volume.restrict (Ioi 0)) :=
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      continuous_criticalMellinChebyshevResolventRayRepresentative.measurable)
      |>.aestronglyMeasurable.restrict
  refine hmajor.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-r * t) *
        |criticalMellinChebyshevResolventRayRepresentative t| =
        Real.exp (-r * t) *
          |criticalMellinChebyshevResolventSource t| := by
      rw [criticalMellinChebyshevResolventRayRepresentative_eq ht.le]
    _ ≤ Real.exp (-r * t) * (B * Real.exp (alpha * t)) := by
      gcongr
      exact hB t ht.le
    _ = B * Real.exp ((alpha - r) * t) := by
      rw [show Real.exp (-r * t) * (B * Real.exp (alpha * t)) =
        B * (Real.exp (-r * t) * Real.exp (alpha * t)) by ring,
        ← Real.exp_add]
      congr 2
      ring

theorem integral_Ioi_exp_mul_unitRieszChebyshevRayIntegral_eq_resolvent_of_exponentialBound
    {alpha B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hrNegOne : -1 < r) (hr : alpha < r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(r + 1) * t) *
      unitRieszChebyshevRayIntegral t) =
      (∫ t in Ioi (0 : ℝ), Real.exp (-r * t) *
        criticalMellinChebyshevResolventRayRepresentative t) +
        (2 / 3) / (r + 1) := by
  have hR :=
    integrableOn_exp_mul_criticalMellinChebyshevResolventRayRepresentative_of_exponentialBound
      hB0 hB hr
  have hA : IntegrableOn (fun t : ℝ =>
      (2 / 3) * Real.exp (-(r + 1) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -(r + 1) < 0 by linarith) 0).const_mul (2 / 3)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t =
        Real.exp (-r * t) *
          criticalMellinChebyshevResolventRayRepresentative t +
            (2 / 3) * Real.exp (-(r + 1) * t) := by
    intro t ht
    rw [unitRieszChebyshevRayIntegral_eq_fullResolvent ht.le,
      criticalMellinChebyshevResolventRayRepresentative_eq ht.le]
    have hcollapse : Real.exp (-(r + 1) * t) * Real.exp t =
        Real.exp (-r * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_add]
    calc
      Real.exp (-(r + 1) * t) *
            (Real.exp t * criticalMellinChebyshevResolventSource t) +
          Real.exp (-(r + 1) * t) * (2 / 3) =
          (Real.exp (-(r + 1) * t) * Real.exp t) *
              criticalMellinChebyshevResolventSource t +
            (2 / 3) * Real.exp (-(r + 1) * t) := by ring
      _ = _ := by rw [hcollapse]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_add hR hA,
    MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (show -(r + 1) < 0 by linarith) 0]
  have hr1 : r + 1 ≠ 0 := by linarith
  rw [show Real.exp (-(r + 1) * 0) = 1 by simp]
  rw [show -(1 : ℝ) / -(r + 1) = 1 / (r + 1) by field_simp [hr1]]
  simp only [div_eq_mul_inv, one_mul]

theorem integral_Ioi_exp_mul_criticalMellinNormalizedChebyshevError_eq_resolvent_of_exponentialBound
    {alpha B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hrHalf : 1 / 2 < r) (hrAlpha : alpha < r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-r * t) *
      criticalMellinNormalizedChebyshevError t) =
      (r + 1) * (∫ t in Ioi (0 : ℝ), Real.exp (-r * t) *
        criticalMellinChebyshevResolventRayRepresentative t) + 2 / 3 := by
  have hprim :=
    integral_Ioi_exp_mul_criticalMellinChebyshevRayDensity_eq_of_exponentialBound
      hB0 hB hrHalf hrAlpha
  have hres :=
    integral_Ioi_exp_mul_unitRieszChebyshevRayIntegral_eq_resolvent_of_exponentialBound
      hB0 hB (by linarith [hrHalf]) hrAlpha
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      Real.exp (-(r + 1) * t) * criticalMellinChebyshevRayDensity t =
        Real.exp (-r * t) * criticalMellinNormalizedChebyshevError t := by
    intro t ht
    rw [criticalMellinChebyshevRayDensity]
    have hcollapse : Real.exp (-(r + 1) * t) * Real.exp t =
        Real.exp (-r * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show Real.exp (-(r + 1) * t) *
        (Real.exp t * criticalMellinNormalizedChebyshevError t) =
        (Real.exp (-(r + 1) * t) * Real.exp t) *
          criticalMellinNormalizedChebyshevError t by ring,
      hcollapse]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, hres] at hprim
  have hr1 : r + 1 ≠ 0 := by linarith [hrHalf]
  field_simp [hr1] at hprim ⊢
  linarith

theorem criticalNormalizedChebyshevErrorLaplace_eq_resolvent_on_real_of_exponentialBound
    {alpha B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hrHalf : 1 / 2 < r) (hrAlpha : alpha < r) :
    criticalNormalizedChebyshevErrorLaplace (r : ℂ) =
      ((r : ℂ) + 1) * criticalMellinChebyshevResolventLaplace (r : ℂ) + 2 / 3 := by
  rw [criticalNormalizedChebyshevErrorLaplace_ofReal,
    criticalMellinChebyshevResolventLaplace_ofReal]
  have hreal :=
    integral_Ioi_exp_mul_criticalMellinNormalizedChebyshevError_eq_resolvent_of_exponentialBound
      hB0 hB hrHalf hrAlpha
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_ofNat] using hc

theorem analyticOnNhd_criticalMellinChebyshevResolventDefectExtension_of_exponentialBound
    {alpha B : ℝ} (halpha : 0 ≤ alpha) (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t)) :
    AnalyticOnNhd ℂ criticalMellinChebyshevResolventDefectExtension
      {u : ℂ | alpha - 1 / 2 < u.re} := by
  have hL :=
    analyticOnNhd_criticalMellinChebyshevResolventLaplace_of_exponentialBound
      hB0 hB
  intro u hu
  change alpha - 1 / 2 < u.re at hu
  have hz : alpha < (u + 1 / 2).re := by
    norm_num [Complex.add_re]
    linarith
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) u := by fun_prop
  have hLcomp : AnalyticAt ℂ
      (fun z : ℂ => criticalMellinChebyshevResolventLaplace (z + 1 / 2)) u :=
    AnalyticAt.comp (f := fun z : ℂ => z + 1 / 2)
      (hL (u + 1 / 2) hz) hshift
  have hden : u + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  change AnalyticAt ℂ (fun z : ℂ =>
    1 / (z + 1) - 1 -
      (z + 1) * (((z + 3 / 2) *
        criticalMellinChebyshevResolventLaplace (z + 1 / 2)) + 2 / 3)) u
  exact ((analyticAt_const.div (analyticAt_id.add analyticAt_const) hden).sub
      analyticAt_const).sub
    ((analyticAt_id.add analyticAt_const).mul
      (((analyticAt_id.add analyticAt_const).mul hLcomp).add analyticAt_const))

theorem criticalMellinChebyshevResolventDefectExtension_eq_regularized_on_real_of_exponentialBound
    {alpha B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t))
    (hr : 0 < r) (hrAlpha : alpha < r + 1 / 2) :
    criticalMellinChebyshevResolventDefectExtension (r : ℂ) =
      regularizedCriticalMellinDefect (r : ℂ) := by
  let z : ℂ := ((r + 1 / 2 : ℝ) : ℂ)
  have hzHalf : 1 / 2 < r + 1 / 2 := by linarith
  have hLap :=
    criticalNormalizedChebyshevErrorLaplace_eq_resolvent_on_real_of_exponentialBound
      hB0 hB hzHalf hrAlpha
  have hzre : 1 / 2 < z.re := by
    dsimp only [z]
    norm_num
    linarith
  have hC50 := criticalNormalizedChebyshevErrorLaplace_eq_logDeriv hzre
  have hmain :
      (((r : ℂ) + 3 / 2) *
          criticalMellinChebyshevResolventLaplace ((r : ℂ) + 1 / 2) + 2 / 3) =
        -(logDeriv zetaResidueUnit ((r : ℂ) + 1) + 1) / ((r : ℂ) + 1) := by
    rw [hLap] at hC50
    dsimp only [z] at hC50
    push_cast at hC50
    convert hC50 using 1 <;> ring
  have hfun : zetaResidueUnit = regularizedRiemannZeta := by
    funext s
    rfl
  have hden : (r : ℂ) + 1 ≠ 0 := by
    apply ne_zero_of_re_pos
    norm_num
    linarith
  have hsolve :
      -((r : ℂ) + 1) *
          (((r : ℂ) + 3 / 2) *
            criticalMellinChebyshevResolventLaplace ((r : ℂ) + 1 / 2) + 2 / 3) - 1 =
        logDeriv zetaResidueUnit ((r : ℂ) + 1) := by
    rw [hmain]
    field_simp [hden]
    ring
  rw [criticalMellinChebyshevResolventDefectExtension,
    regularizedCriticalMellinDefect, ← hfun, ← hsolve]
  ring

theorem criticalMellinChebyshevResolventDefectExtension_eq_regularized_of_exponentialBound
    {alpha B : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t)) :
    ∀ u : ℂ, 0 < u.re →
      criticalMellinChebyshevResolventDefectExtension u =
        regularizedCriticalMellinDefect u := by
  let U : Set ℂ := {u : ℂ | 0 < u.re}
  have hAfull :=
    analyticOnNhd_criticalMellinChebyshevResolventDefectExtension_of_exponentialBound
      halpha hB0 hB
  have hA : AnalyticOnNhd ℂ criticalMellinChebyshevResolventDefectExtension U :=
    hAfull.mono (by
      intro u hu
      change 0 < u.re at hu
      change alpha - 1 / 2 < u.re
      linarith)
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  have htwo : (2 : ℂ) ∈ U := by
    change 0 < (2 : ℂ).re
    norm_num
  have htend : Tendsto (fun r : ℝ => (r : ℂ))
      (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => (r : ℂ))
          (𝓝 (2 : ℝ)) (𝓝 (2 : ℂ)) := by
        simpa using Complex.continuous_ofReal.tendsto (2 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hcon
      have : r = 2 := by exact_mod_cast hcon
      exact absurd this (ne_of_gt hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      criticalMellinChebyshevResolventDefectExtension z =
        regularizedCriticalMellinDefect z := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    change (2 : ℝ) < r at hr
    exact criticalMellinChebyshevResolventDefectExtension_eq_regularized_on_real_of_exponentialBound
      hB0 hB (lt_trans (by norm_num) hr) (by linarith)
  have heq := hA.eqOn_of_preconnected_of_frequently_eq hR
    (convex_halfSpace_re_gt 0).isPreconnected htwo hfreq
  intro u hu
  exact heq hu

theorem xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound
    {alpha B : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hB0 : 0 ≤ B)
    (hbound : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B * Real.exp (alpha * t)) :
    XiZeroHalfPlaneBound alpha := by
  let A : ℂ → ℂ := criticalMellinChebyshevResolventDefectExtension
  have hA : AnalyticOnNhd ℂ A {u : ℂ | alpha - 1 / 2 < u.re} :=
    analyticOnNhd_criticalMellinChebyshevResolventDefectExtension_of_exponentialBound
      halpha hB0 hbound
  have hAagree : ∀ u : ℂ, 0 < u.re →
      A u = regularizedCriticalMellinDefect u :=
    criticalMellinChebyshevResolventDefectExtension_eq_regularized_of_exponentialBound
      halpha halphaHalf hB0 hbound
  let D : ℂ → ℂ := fun w =>
    -I * (A (-1 / 2 - I * w) +
      gammaRealLogConnection (1 / 2 - I * w))
  have hD : AnalyticOnNhd ℂ D (ccmXiUpperHalfPlaneAbove alpha) := by
    intro w hw
    change alpha < w.im at hw
    have hs : alpha - 1 / 2 < (-1 / 2 - I * w).re := by
      simp [mul_re]
      linarith
    have hinner : AnalyticAt ℂ (fun z : ℂ => -1 / 2 - I * z) w := by
      fun_prop
    have hAcomp : AnalyticAt ℂ (fun z : ℂ => A (-1 / 2 - I * z)) w :=
      AnalyticAt.comp (f := fun z : ℂ => -1 / 2 - I * z)
        (hA _ hs) hinner
    have hgammaArg : 0 < ((1 / 2 - I * w) / 2).re := by
      norm_num [Complex.div_re, mul_re]
      linarith
    have hgammaBase : AnalyticAt ℂ Complex.digamma ((1 / 2 - I * w) / 2) :=
      digamma_analyticOnNhd_re_pos _ hgammaArg
    have hgammaInner : AnalyticAt ℂ (fun z : ℂ => (1 / 2 - I * z) / 2) w := by
      fun_prop
    have hgammaComp : AnalyticAt ℂ
        (fun z : ℂ => Complex.digamma ((1 / 2 - I * z) / 2)) w :=
      AnalyticAt.comp (f := fun z : ℂ => (1 / 2 - I * z) / 2)
        hgammaBase hgammaInner
    have hconn : AnalyticAt ℂ
        (fun z : ℂ => gammaRealLogConnection (1 / 2 - I * z)) w := by
      unfold gammaRealLogConnection
      fun_prop
    exact analyticAt_const.mul (hAcomp.add hconn)
  have hDagree : ∀ w : ℂ, 1 / 2 < w.im → D w = logDeriv XiC w := by
    intro w hw
    let z : ℂ := -w
    let s : ℂ := 1 / 2 + z * I
    have hsre : 1 < s.re := by
      dsimp only [s, z]
      simp [mul_re]
      linarith
    have hspos : 0 < s.re := lt_trans zero_lt_one hsre
    have hs0 : s ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      rw [Complex.zero_re] at hre
      linarith
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [Complex.one_re] at hre
      linarith
    have hzeta : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re hsre
    have htrace : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
      rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
        hspos hs1 hzeta]
      exact (logDeriv_XiC_eq_relativeResolventTrace
        (by
          change xi s ≠ 0
          rw [xi_eq_archFactor_mul_zeta hs0 hs1
            (Gammaℝ_ne_zero_of_re_pos hspos)]
          exact mul_ne_zero
            (archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)) hzeta)).symm
    have hsource := continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma
      hspos hs0 hs1
    have hcoord : xiCriticalMellinCoordinate z = -1 / 2 - I * w := by
      dsimp only [xiCriticalMellinCoordinate, z]
      ring
    have hgammaCoord : 1 / 2 + z * I = 1 / 2 - I * w := by
      dsimp only [z]
      ring
    have hdefRe : 0 < (-1 / 2 - I * w).re := by
      simp [mul_re]
      linarith
    have hdef := hAagree (-1 / 2 - I * w) hdefRe
    have hreg := regularizedCriticalMellinDefect_eq_continued hdefRe
    dsimp only [D]
    rw [hdef]
    have hsource' :
        continuedPrimeArchSourceRelativeTrace z =
          I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
            gammaRealLogConnection (1 / 2 - I * w)) := by
      rw [hsource, continuedMellinGammaSourceTrace, hcoord, hgammaCoord]
      rw [← hreg]
    rw [hsource'] at htrace
    rw [show logDeriv XiC z = -logDeriv XiC w by
      dsimp only [z]
      rw [logDeriv_XiC_neg]] at htrace
    calc
      -I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
          gammaRealLogConnection (1 / 2 - I * w)) =
          -(I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
            gammaRealLogConnection (1 / 2 - I * w))) := by ring
      _ = -(-logDeriv XiC w) := by rw [htrace]
      _ = logDeriv XiC w := neg_neg _
  exact xiZeroHalfPlaneBound_of_upper_logDeriv_extensionAbove D hD hDagree

theorem xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventExponentialBounded
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hbound : CriticalMellinChebyshevResolventExponentialBounded alpha) :
    XiZeroHalfPlaneBound alpha := by
  obtain ⟨B, hB0, hB⟩ := hbound
  exact xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound
    halpha halphaHalf hB0 hB

end GaloisForLFunctions.RHTower
