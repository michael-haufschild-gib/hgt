import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPairedEtaApproximation
import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteDeflation
import GaloisForLFunctions.RHTower.LiClockCentralTraceSineContinuity
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedEndpoint
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedResolvent
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Damped signed areas of literal finite eta clocks

Uniform central-source approximation transfers the full-copy positive resolvent to logarithmically
growing finite windows. The actual source frequency envelope gives an explicit weighted tail bound.
The source-defined finite deflated response cancels the removed pole area before taking limits;
at damping two its centered area tends to the exact arithmetic endpoint intercept.

These signed aggregate laws do not assert pointwise clock positivity or the Riemann hypothesis.
-/

open Complex Set Metric Filter Topology MeasureTheory
namespace RHTower
noncomputable section

/-- The literal logarithmic clock endpoint of one finite prefix. -/
def liClockPairedEtaClockWindow (c : ℝ) (N : ℕ) : ℝ :=
  c*Real.log (2*(N:ℝ)+1)

/-- Signed damped area of the literal finite completed-clock response. -/
def liClockPairedEtaDampedClockWindowArea (N : ℕ) (r c p : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..liClockPairedEtaClockWindow c N,
    Real.exp (-p*t)*(liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re

/-- Signed damped area of the source-defined finite deflated response. -/
def liClockPairedEtaDampedDeflatedWindowArea (N : ℕ) (r c p : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..liClockPairedEtaClockWindow c N,
    Real.exp (-p*t)*(liClockPairedEtaFiniteDeflatedClockResponse N r (t:ℂ)).re

/-- Literal finite weighted area of the removed eta compensation pole. -/
def liClockPairedEtaDampedPoleWindowArea (p L : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..L, Real.exp (-p*t)*(2*Real.sinh (2*t))

private theorem clockWindow_nonneg {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    0 ≤ liClockPairedEtaClockWindow c N := by
  apply mul_nonneg hc
  apply Real.log_nonneg
  have hN : 0 ≤ (N : ℝ) := by positivity
  linarith

private theorem clockWindow_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (liClockPairedEtaClockWindow c) atTop atTop := by
  have hodd : Tendsto (fun N : ℕ => 2*(N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  exact (Real.tendsto_log_atTop.comp hodd).const_mul_atTop hc

/-- Quantitative finite denominator validity gives continuous real clocks and actual weighted integrals. -/
theorem continuous_liClockPairedEtaFiniteClockResponse_re (N : ℕ)
    (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1/128) :
    Continuous (fun t : ℝ => (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re) := by
  have heta (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
      RiemannGaussian.pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 := by
    have hn : ‖z‖ ≤ 1/128 :=
      (show ‖z‖ = r by simpa only [mem_sphere_iff_norm, sub_zero] using hz).le.trans hrsmall
    have hfloor := liClockPairedEtaFiniteCore_re_gt_one_sixteenth N hsmall hn
    intro hzero
    norm_num [hzero] at hfloor
  have hT := continuousOn_liClockPairedEtaFiniteSourceTrace_sphere N hrsmall heta
  have hclock := continuous_liClockCentralTraceSineContour hr hT
  change Continuous (fun t : ℝ =>
    (liClockCentralTraceSineContour (liClockPairedEtaFiniteSourceTrace N) r (t:ℂ)).re)
  exact Complex.continuous_re.comp (hclock.comp Complex.continuous_ofReal)

private theorem liClockWeightedWindow_difference_le {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {p L δ : ℝ}
    (hp : 0 < p) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hfg : ∀ t ∈ Icc 0 L, |f t - g t| ≤ δ) :
    |(∫ t in 0..L, Real.exp (-p * t) * f t) -
      (∫ t in 0..L, Real.exp (-p * t) * g t)| ≤ δ / p := by
  have hc : Continuous (fun t : ℝ => Real.exp (-p * t)) := by fun_prop
  have hif : IntervalIntegrable (fun t => Real.exp (-p * t) * f t) volume 0 L :=
    (hc.mul hf).intervalIntegrable 0 L
  have hig : IntervalIntegrable (fun t => Real.exp (-p * t) * g t) volume 0 L :=
    (hc.mul hg).intervalIntegrable 0 L
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f :=
    fun t : ℝ => Real.exp (-p * t) * (f t - g t)) (g := fun t => δ * Real.exp (-p * t))
    hL (Filter.Eventually.of_forall fun t ht => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      calc
        Real.exp (-p * t) * |f t - g t| ≤ Real.exp (-p * t) * δ :=
          mul_le_mul_of_nonneg_left (hfg t ⟨le_of_lt ht.1, ht.2⟩) (Real.exp_pos _).le
        _ = δ * Real.exp (-p * t) := mul_comm _ _)
    ((continuous_const.mul hc).intervalIntegrable 0 L)
  have hD (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-p * t) / (-p))
      (Real.exp (-p * x)) x := by
    simpa only [Function.comp_def, mul_one, mul_div_cancel_right₀ _ (neg_ne_zero.mpr hp.ne')] using
      (((Real.hasDerivAt_exp (-p * x)).comp x
        ((hasDerivAt_id x).const_mul (-p))).div_const (-p))
  have hexp : (∫ t in 0..L, Real.exp (-p * t)) = (1 - Real.exp (-p * L)) / p := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x)
      (hc.intervalIntegrable 0 L)]
    simp only [mul_zero, Real.exp_zero]
    field_simp
    ring_nf
  have hdiff : (∫ t in 0..L, Real.exp (-p * t) * (f t - g t)) =
      (∫ t in 0..L, Real.exp (-p * t) * f t) -
        (∫ t in 0..L, Real.exp (-p * t) * g t) := by
    simp only [mul_sub, intervalIntegral.integral_sub hif hig]
  rw [Real.norm_eq_abs, hdiff, intervalIntegral.integral_const_mul, hexp] at hbound
  refine hbound.trans ?_
  calc
    δ * ((1 - Real.exp (-p * L)) / p) ≤ δ * (1 / p) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      exact (div_le_div_iff_of_pos_right hp).2 (by linarith [Real.exp_pos (-p * L)])
    _ = δ / p := by ring_nf

private theorem liClockLinearExpTail_hasDerivAt {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -Real.exp (-κ * t) * (t / κ + 1 / κ ^ 2))
      (x * Real.exp (-κ * x)) x := by
  convert! ((((Real.hasDerivAt_exp (-κ * x)).comp x
    ((hasDerivAt_id x).const_mul (-κ))).neg).mul
      (((hasDerivAt_id x).div_const κ).add_const (1 / κ ^ 2))) using 1
  change x * Real.exp (-κ * x) =
    -(Real.exp (-κ * x) * (-κ * 1)) * (x / κ + 1 / κ ^ 2) +
      -Real.exp (-κ * x) * (1 / κ)
  field_simp [hκ.ne']
  ring_nf

private theorem liClockLinearExpTail_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => -Real.exp (-κ * t) * (t / κ + 1 / κ ^ 2))
      atTop (𝓝 0) := by
  have hscale : Tendsto (fun t : ℝ => κ * t) atTop atTop :=
    tendsto_id.const_mul_atTop hκ
  have hlinear := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  convert (hlinear.const_mul (-(1 / κ ^ 2))).add
    (hexp.const_mul (-(1 / κ ^ 2))) using 1
  · ext t
    simp only [Function.comp_apply, pow_one]
    field_simp [hκ.ne']
    ring_nf
  · simp

private theorem liClockLinearExpTail_integrableOn {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-κ * t)) (Ioi L) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => liClockLinearExpTail_hasDerivAt hκ x)
    (fun x hx => mul_nonneg (hL.trans hx.le) (Real.exp_pos _).le)
    (liClockLinearExpTail_tendsto hκ)

private theorem liClockLinearExpTail_integral {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) :
    (∫ t : ℝ in Ioi L, t * Real.exp (-κ * t)) =
      Real.exp (-κ * L) * (L / κ + 1 / κ ^ 2) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x _ => liClockLinearExpTail_hasDerivAt hκ x)
    (fun x hx => mul_nonneg (hL.trans hx.le) (Real.exp_pos _).le)
    (liClockLinearExpTail_tendsto hκ)
  simpa only [zero_sub, neg_mul, neg_neg] using h

private theorem liClockEtaPole_weighted_area (L : ℝ) :
    (∫ t in 0..L, Real.exp (-2 * t) * (2 * Real.sinh (2 * t))) =
      L - (1 - Real.exp (-4 * L)) / 4 := by
  have hkernel (t : ℝ) : Real.exp (-2 * t) * (2 * Real.sinh (2 * t)) =
      1 - Real.exp (-4 * t) := by
    rw [Real.sinh_eq]
    calc
      Real.exp (-2 * t) * (2 * ((Real.exp (2 * t) - Real.exp (-(2 * t))) / 2)) =
          Real.exp (-2 * t) * Real.exp (2 * t) - Real.exp (-2 * t) * Real.exp (-(2 * t)) := by ring_nf
      _ = 1 - Real.exp (-4 * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        have hzero : -2 * t + 2 * t = 0 := by ring_nf
        have hsum : -2 * t + -(2 * t) = -4 * t := by ring_nf
        rw [hzero, hsum, Real.exp_zero]
  have hD (x : ℝ) : HasDerivAt (fun t : ℝ => t + Real.exp (-4 * t) / 4)
      (1 - Real.exp (-4 * x)) x := by
    convert! (hasDerivAt_id x).add
      (((Real.hasDerivAt_exp (-4 * x)).comp x
        ((hasDerivAt_id x).const_mul (-4))).div_const 4) using 1
    ring_nf
  have hc : Continuous (fun t : ℝ => 1 - Real.exp (-4 * t)) := by fun_prop
  simp_rw [hkernel]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x)
    (hc.intervalIntegrable 0 L)]
  simp only [mul_zero, Real.exp_zero, zero_add]
  ring_nf

private theorem finiteClock_window_error_le (N : ℕ) {r L : ℝ}
    (hr : 0 < r) (_hL : 0 ≤ L)
    (herror : ∀ t : ℂ,
      ‖liClockPairedEtaFiniteClockResponse N r t-liEvenCrossActualComplexClockResponse t‖ ≤
        liClockPairedEtaSourceErrorEnvelope N*Real.sinh (‖t‖/r)) :
    ∀ t ∈ Icc 0 L,
      |(liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re-
        liEvenCrossActualClockResponse t| ≤
        liClockPairedEtaSourceErrorEnvelope N*Real.sinh (L/r) := by
  intro t ht
  have he := herror (t:ℂ)
  simp only [liEvenCrossActualComplexClockResponse_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht.1] at he
  have hre := Complex.abs_re_le_norm
    (liClockPairedEtaFiniteClockResponse N r (t:ℂ)-(liEvenCrossActualClockResponse t:ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  refine (hre.trans he).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sinh_le_sinh.mpr (div_le_div_of_nonneg_right ht.2 hr.le))
    (liClockPairedEtaSourceErrorEnvelope_nonneg N)

private theorem finiteClock_area_difference_le (N : ℕ) {r c p : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/128) (hc : 0 ≤ c) (hp : 0 < p)
    (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    (herror : ∀ t : ℂ,
      ‖liClockPairedEtaFiniteClockResponse N r t-liEvenCrossActualComplexClockResponse t‖ ≤
        liClockPairedEtaSourceErrorEnvelope N*Real.sinh (‖t‖/r)) :
    |liClockPairedEtaDampedClockWindowArea N r c p -
      (∫ t in (0:ℝ)..liClockPairedEtaClockWindow c N,
        Real.exp (-p*t)*liEvenCrossActualClockResponse t)| ≤
      liClockPairedEtaSourceErrorEnvelope N *
        Real.sinh (liClockPairedEtaClockWindow c N/r)/p := by
  exact liClockWeightedWindow_difference_le
    (continuous_liClockPairedEtaFiniteClockResponse_re N hsmall hr hrsmall)
    continuous_liEvenCrossActualClockResponse hp (clockWindow_nonneg hc N)
    (mul_nonneg (liClockPairedEtaSourceErrorEnvelope_nonneg N)
      (Real.sinh_nonneg_iff.mpr (div_nonneg (clockWindow_nonneg hc N) hr.le)))
    (finiteClock_window_error_le N hr (clockWindow_nonneg hc N) herror)

private theorem finiteClock_area_difference_tendsto {r c p : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/128) (hc : 0 < c) (hcr : c < r/4)
    (hp : 0 < p)
    (herror : ∀ N : ℕ, 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16 → ∀ t : ℂ,
      ‖liClockPairedEtaFiniteClockResponse N r t-liEvenCrossActualComplexClockResponse t‖ ≤
        liClockPairedEtaSourceErrorEnvelope N*Real.sinh (‖t‖/r)) :
    Tendsto (fun N => liClockPairedEtaDampedClockWindowArea N r c p-
      (∫ t in (0:ℝ)..liClockPairedEtaClockWindow c N,
        Real.exp (-p*t)*liEvenCrossActualClockResponse t)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _))
  · filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth] with N hsmall
    simpa only [Real.norm_eq_abs] using
      finiteClock_area_difference_le N hr hrsmall hc.le hp hsmall (herror N hsmall)
  · simpa only [zero_div, liClockPairedEtaClockWindow] using
      (liClockPairedEtaSourceErrorEnvelope_mul_sinh_tendsto_zero hr hc hcr).div_const p

/-- Actual truncated damped areas tend to the full-copy signed resolvent. -/
theorem liEvenCrossActualClock_dampedWindow_tendsto {c p : ℝ}
    (hc : 0 < c) (hp : 1/300 < p) :
    Tendsto (fun N => ∫ t in (0:ℝ)..liClockPairedEtaClockWindow c N,
      Real.exp (-p*t)*liEvenCrossActualClockResponse t) atTop
      (𝓝 (liEvenCrossActualClockDampedResolvent p)) := by
  rw [← liEvenCrossActualClockDampedResponse_integral_eq_resolvent hp]
  exact intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_liEvenCrossActualClockDampedResponse hp) (clockWindow_tendsto_atTop hc)

/-- One valid source radius controls every positive damped logarithmic window. -/
theorem exists_liClockPairedEtaDampedClockWindowArea_tendsto :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ c : ℝ, 0 < c → c < r/4 → ∀ p : ℝ, 1/300 < p →
        Tendsto (fun N => liClockPairedEtaDampedClockWindowArea N r c p) atTop
          (𝓝 (liEvenCrossActualClockDampedResolvent p)) := by
  obtain ⟨r₀, hr₀, hr₀small, herror⟩ := exists_liClockPairedEtaFiniteClockResponse_error_radius
  refine ⟨r₀, hr₀, hr₀small, fun r hr hrr c hc hcr p hp => ?_⟩
  have hd := finiteClock_area_difference_tendsto hr (hrr.le.trans hr₀small) hc hcr
    (by linarith : 0 < p) (herror r hr hrr)
  have ha := liEvenCrossActualClock_dampedWindow_tendsto hc hp
  simpa only [zero_add, sub_add_cancel] using hd.add ha

/-- Explicit actual weighted tail from the source frequency envelope. -/
theorem liEvenCrossActualClockDampedResponse_tail_le {p L : ℝ}
    (hp : 1/300 < p) (hL : 0 ≤ L) :
    |∫ t : ℝ in Ioi L, Real.exp (-p*t)*liEvenCrossActualClockResponse t| ≤
      xiShiftAbsoluteMass 0*Real.exp (-(p-1/300)*L)*
        (L/(p-1/300)+1/(p-1/300)^2) := by
  have hκ : 0 < p-1/300 := by linarith
  have hf : IntegrableOn (fun t : ℝ => Real.exp (-p*t)*liEvenCrossActualClockResponse t)
      (Ioi L) :=
    (integrableOn_liEvenCrossActualClockDampedResponse hp).mono_set (Ioi_subset_Ioi hL)
  have hg := (liClockLinearExpTail_integrableOn hκ hL).const_mul (xiShiftAbsoluteMass 0)
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ t : ℝ in Ioi L, Real.exp (-p*t)*liEvenCrossActualClockResponse t‖ ≤
        ∫ t : ℝ in Ioi L, ‖Real.exp (-p*t)*liEvenCrossActualClockResponse t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi L, xiShiftAbsoluteMass 0*(t*Real.exp (-(p-1/300)*t)) := by
      apply integral_mono_ae hf.norm hg
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        have ht0 : 0 ≤ t := hL.trans ht.le
        dsimp only
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        have hb := mul_le_mul_of_nonneg_left
          (norm_liEvenCrossActualClockResponse_le_mass_mul_exp ht0)
          (Real.exp_pos (-p*t)).le
        refine hb.trans_eq ?_
        rw [show Real.exp (-p*t)*(xiShiftAbsoluteMass 0*t*Real.exp (t/300)) =
          xiShiftAbsoluteMass 0*(t*(Real.exp (-p*t)*Real.exp (t/300))) by ring_nf,
          ← Real.exp_add]
        congr 3
        ring_nf
    _ = xiShiftAbsoluteMass 0*Real.exp (-(p-1/300)*L)*
        (L/(p-1/300)+1/(p-1/300)^2) := by
      rw [integral_const_mul, liClockLinearExpTail_integral hκ hL]
      ring_nf

/-- At damping two the source resolvent is exactly the arithmetic endpoint curvature. -/
theorem liEvenCrossActualClockDampedResolvent_two_eq_endpoint :
    liEvenCrossActualClockDampedResolvent 2 = xiEndpointCompletedCurvature/4 := by
  rw [← liEvenCrossActualClockDampedResponse_integral_eq_resolvent (by norm_num : (1/300:ℝ)<2)]
  exact integral_liEvenCrossActualClock_dampedEndpoint

private theorem finiteClock_eta_nonzero (N : ℕ)
    (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    {r : ℝ} (hrsmall : r ≤ 1/128) (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
    RiemannGaussian.pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 := by
  have hn : ‖z‖ ≤ 1/128 :=
    (show ‖z‖ = r by simpa only [mem_sphere_iff_norm, sub_zero] using hz).le.trans hrsmall
  have hfloor := liClockPairedEtaFiniteCore_re_gt_one_sixteenth N hsmall hn
  intro hzero
  norm_num [hzero] at hfloor

/-- The actual finite deflated source response differs by the explicit removed pole clock. -/
theorem liClockPairedEtaFiniteDeflatedClockResponse_re_eq (N : ℕ)
    (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1/128) (t : ℝ) :
    (liClockPairedEtaFiniteDeflatedClockResponse N r (t:ℂ)).re =
      (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re + 2*Real.sinh (2*t) := by
  have hsinh : Complex.sinh (2*(t:ℂ)) = (Real.sinh (2*t):ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (Complex.ofReal_sinh (2*t)).symm
  have h := congrArg Complex.re
    (liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated N hr
      (by linarith : r < 1/2) (finiteClock_eta_nonzero N hsmall hrsmall) (t:ℂ))
  have hsinhRe := congrArg Complex.re hsinh
  simp only [Complex.ofReal_re] at hsinhRe
  norm_num [Complex.add_re, Complex.mul_re] at h
  rw [hsinhRe] at h
  linarith

/-- Renormalization is exact on each finite prefix, before any improper limit is taken. -/
theorem liClockPairedEtaDampedDeflatedWindowArea_sub_pole (N : ℕ)
    (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1/128) (c p : ℝ) :
    liClockPairedEtaDampedDeflatedWindowArea N r c p -
      liClockPairedEtaDampedPoleWindowArea p (liClockPairedEtaClockWindow c N) =
      liClockPairedEtaDampedClockWindowArea N r c p := by
  have hc : Continuous (fun t : ℝ => Real.exp (-p*t)) := by fun_prop
  have hf : Continuous (fun t : ℝ => Real.exp (-p*t)*
      (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re) :=
    hc.mul (continuous_liClockPairedEtaFiniteClockResponse_re N hsmall hr hrsmall)
  have hpole : Continuous (fun t : ℝ => Real.exp (-p*t)*(2*Real.sinh (2*t))) := by fun_prop
  have hdef : (fun t : ℝ => Real.exp (-p*t)*
      (liClockPairedEtaFiniteDeflatedClockResponse N r (t:ℂ)).re) =
      (fun t : ℝ => Real.exp (-p*t)*(liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re+
        Real.exp (-p*t)*(2*Real.sinh (2*t))) := by
    funext t
    rw [liClockPairedEtaFiniteDeflatedClockResponse_re_eq N hsmall hr hrsmall t]
    ring_nf
  unfold liClockPairedEtaDampedDeflatedWindowArea liClockPairedEtaDampedPoleWindowArea
    liClockPairedEtaDampedClockWindowArea
  rw [hdef, intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hpole.intervalIntegrable _ _)]
  ring_nf

/-- The removed pole has an exact elementary area at endpoint damping. -/
theorem liClockPairedEtaDampedPoleWindowArea_two (L : ℝ) :
    liClockPairedEtaDampedPoleWindowArea 2 L = L-(1-Real.exp (-4*L))/4 :=
  liClockEtaPole_weighted_area L

/-- One actual radius gives positive finite areas and all-damping deflated cancellation,
including both arithmetic endpoint limits. -/
theorem exists_liClockPairedEtaDampedWindow_sum_rules :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ c : ℝ, 0 < c → c < r/4 →
        (∀ p : ℝ, 1/300 < p →
          Tendsto (fun N => liClockPairedEtaDampedClockWindowArea N r c p) atTop
            (𝓝 (liEvenCrossActualClockDampedResolvent p)) ∧
          (∀ᶠ N : ℕ in atTop, 0 < liClockPairedEtaDampedClockWindowArea N r c p) ∧
          Tendsto (fun N => liClockPairedEtaDampedDeflatedWindowArea N r c p-
            liClockPairedEtaDampedPoleWindowArea p (liClockPairedEtaClockWindow c N)) atTop
            (𝓝 (liEvenCrossActualClockDampedResolvent p))) ∧
        Tendsto (fun N => liClockPairedEtaDampedClockWindowArea N r c 2) atTop
          (𝓝 (xiEndpointCompletedCurvature/4)) ∧
        Tendsto (fun N => liClockPairedEtaDampedDeflatedWindowArea N r c 2-
          liClockPairedEtaClockWindow c N) atTop
          (𝓝 ((xiEndpointCompletedCurvature-1)/4)) := by
  obtain ⟨r₀, hr₀, hr₀small, harea⟩ := exists_liClockPairedEtaDampedClockWindowArea_tendsto
  refine ⟨r₀, hr₀, hr₀small, fun r hr hrr c hc hcr => ?_⟩
  have hrsmall : r ≤ 1/128 := hrr.le.trans hr₀small
  have hrenorm (p : ℝ) (hp : 1/300 < p) :
      Tendsto (fun N => liClockPairedEtaDampedDeflatedWindowArea N r c p-
        liClockPairedEtaDampedPoleWindowArea p (liClockPairedEtaClockWindow c N)) atTop
        (𝓝 (liEvenCrossActualClockDampedResolvent p)) := by
    apply (harea r hr hrr c hc hcr p hp).congr'
    filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth] with N hsmall
    exact (liClockPairedEtaDampedDeflatedWindowArea_sub_pole N hsmall hr hrsmall c p).symm
  have hp2 : (1/300:ℝ) < 2 := by norm_num
  have hend := harea r hr hrr c hc hcr 2 hp2
  rw [liEvenCrossActualClockDampedResolvent_two_eq_endpoint] at hend
  refine ⟨?_, hend, ?_⟩
  · intro p hp
    have ht := harea r hr hrr c hc hcr p hp
    exact ⟨ht, ht.eventually (eventually_gt_nhds
      (liEvenCrossActualClockDampedResolvent_pos (by linarith))), hrenorm p hp⟩
  · have hexp : Tendsto (fun N => Real.exp (-4*liClockPairedEtaClockWindow c N)) atTop (𝓝 0) := by
      convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((clockWindow_tendsto_atTop hc).const_mul_atTop (by norm_num : (0:ℝ)<4)) using 1
      funext N
      congr 1
      ring_nf
    have hpole : Tendsto (fun N =>
        liClockPairedEtaDampedPoleWindowArea 2 (liClockPairedEtaClockWindow c N)-
          liClockPairedEtaClockWindow c N) atTop (𝓝 (-(1/4:ℝ))) := by
      simp_rw [liClockPairedEtaDampedPoleWindowArea_two]
      convert (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hexp).div_const 4).neg using 1
      · funext N
        ring_nf
      · norm_num
    have hren := hrenorm 2 hp2
    rw [liEvenCrossActualClockDampedResolvent_two_eq_endpoint] at hren
    convert hren.add hpole using 1
    · funext N
      ring_nf
    · ring_nf

private theorem finiteClock_area_resolvent_error_le (N : ℕ) {r c p : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/128) (hc : 0 ≤ c) (hp : 1/300 < p)
    (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    (herror : ∀ t : ℂ,
      ‖liClockPairedEtaFiniteClockResponse N r t-liEvenCrossActualComplexClockResponse t‖ ≤
        liClockPairedEtaSourceErrorEnvelope N*Real.sinh (‖t‖/r)) :
    |liClockPairedEtaDampedClockWindowArea N r c p-liEvenCrossActualClockDampedResolvent p| ≤
      liClockPairedEtaSourceErrorEnvelope N*Real.sinh (liClockPairedEtaClockWindow c N/r)/p+
        xiShiftAbsoluteMass 0*Real.exp (-(p-1/300)*liClockPairedEtaClockWindow c N)*
          (liClockPairedEtaClockWindow c N/(p-1/300)+1/(p-1/300)^2) := by
  have hL := clockWindow_nonneg hc N
  have hi := integrableOn_liEvenCrossActualClockDampedResponse hp
  have htail : IntegrableOn (fun t : ℝ => Real.exp (-p*t)*liEvenCrossActualClockResponse t)
      (Ioi (liClockPairedEtaClockWindow c N)) := hi.mono_set (Ioi_subset_Ioi hL)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi htail
  rw [liEvenCrossActualClockDampedResponse_integral_eq_resolvent hp] at hsplit
  have hd := finiteClock_area_difference_le (p:=p) N hr hrsmall hc (by linarith : 0 < p) hsmall herror
  have ht := liEvenCrossActualClockDampedResponse_tail_le hp hL
  calc
    _ = |(liClockPairedEtaDampedClockWindowArea N r c p-
        (∫ t in (0:ℝ)..liClockPairedEtaClockWindow c N,
          Real.exp (-p*t)*liEvenCrossActualClockResponse t))+
        -(∫ t : ℝ in Ioi (liClockPairedEtaClockWindow c N),
          Real.exp (-p*t)*liEvenCrossActualClockResponse t)| := by
      congr 1
      linarith only [hsplit]
    _ ≤ |liClockPairedEtaDampedClockWindowArea N r c p-
        (∫ t in (0:ℝ)..liClockPairedEtaClockWindow c N,
          Real.exp (-p*t)*liEvenCrossActualClockResponse t)|+
        |∫ t : ℝ in Ioi (liClockPairedEtaClockWindow c N),
          Real.exp (-p*t)*liEvenCrossActualClockResponse t| := by
      simpa only [abs_neg] using abs_add_le
        (liClockPairedEtaDampedClockWindowArea N r c p-
          (∫ t in (0:ℝ)..liClockPairedEtaClockWindow c N,
            Real.exp (-p*t)*liEvenCrossActualClockResponse t))
        (-(∫ t : ℝ in Ioi (liClockPairedEtaClockWindow c N),
          Real.exp (-p*t)*liEvenCrossActualClockResponse t))
    _ ≤ _ := add_le_add hd ht

/-- Uniform finite-source error and the complete weighted tail give a quantitative area bound. -/
theorem exists_liClockPairedEtaDampedClockWindowArea_error_bound :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ c : ℝ, 0 ≤ c → ∀ p : ℝ, 1/300 < p → ∀ N : ℕ,
        3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16 →
        |liClockPairedEtaDampedClockWindowArea N r c p-liEvenCrossActualClockDampedResolvent p| ≤
          liClockPairedEtaSourceErrorEnvelope N*Real.sinh (liClockPairedEtaClockWindow c N/r)/p+
            xiShiftAbsoluteMass 0*Real.exp (-(p-1/300)*liClockPairedEtaClockWindow c N)*
              (liClockPairedEtaClockWindow c N/(p-1/300)+1/(p-1/300)^2) := by
  obtain ⟨r₀, hr₀, hr₀small, herror⟩ := exists_liClockPairedEtaFiniteClockResponse_error_radius
  exact ⟨r₀, hr₀, hr₀small, fun r hr hrr c hc p hp N hsmall =>
    finiteClock_area_resolvent_error_le N hr (hrr.le.trans hr₀small) hc hp hsmall
      (herror r hr hrr N hsmall)⟩

end
end RHTower
