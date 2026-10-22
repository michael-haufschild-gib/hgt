import GaloisForLFunctions.RHTower.CCM.CCMExponentialRampArithmeticEnergy
import GaloisForLFunctions.RHTower.ChebyshevDeficitPrimitiveOneSidedRH
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitWeilEnergy
import GaloisForLFunctions.RHTower.WeilLagFunctionOmega
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Signed oscillation of the actual prime-deficit flux

The literal incoming deficit and complete exponential-ramp action take both
signs cofinally, with a fixed nonzero threshold, unconditionally. Under RH,
the stable flux equation constructs their asymptotic Bohr model from every
multiplicity copy of the Weil lag. Its frequency transfer preserves each
coefficient's modulus. If RH fails, the existing one-sided Landau theorem
excludes either eventual finite one-sided bound.

This rules out eventual one-sign ramp dominance. It does not bound the
signed action or prove the canonical-head Gamma--prime--polar inequality.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology ComplexConjugate
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
namespace RHTower

/-- Stable-filter coefficient of the complete multiplicity-copy Weil lag. -/
def ccmPrimeDeficitBohrStateCoeff (q : XiZeroCopy) : ℂ :=
  (cosWeight q : ℂ) / (1 / 2 + (zeroOrdinate q : ℂ) * Complex.I)

/-- Full stable state; no divisor copy is discarded. -/
def ccmPrimeDeficitBohrState : ℝ → ℂ :=
  expSeriesCarrier ccmPrimeDeficitBohrStateCoeff zeroOrdinate

/-- Real signed source selected by the actual incoming/outgoing flux equation. -/
def ccmPrimeDeficitBohrIncoming (t : ℝ) : ℝ :=
  (ccmPrimeDeficitBohrState t).re - weilLagFunctionReal t

private theorem state_den_ne (q : XiZeroCopy) :
    (1 / 2 + (zeroOrdinate q : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

private theorem state_coeff_bound (q : XiZeroCopy) :
    ‖ccmPrimeDeficitBohrStateCoeff q‖ ≤ 2 * cosWeight q := by
  have hr : (1 / 2 : ℝ) ≤ ‖(1 / 2 : ℂ) + (zeroOrdinate q : ℂ) * Complex.I‖ := by
    simpa using Complex.re_le_norm ((1 / 2 : ℂ) + (zeroOrdinate q : ℂ) * Complex.I)
  rw [ccmPrimeDeficitBohrStateCoeff, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cosWeight_pos q)]
  apply (div_le_iff₀ (norm_pos_iff.mpr (state_den_ne q))).mpr
  nlinarith [cosWeight_pos q]

private theorem summable_state_coeff (hRH : RiemannHypothesis) :
    Summable fun q => ‖ccmPrimeDeficitBohrStateCoeff q‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    state_coeff_bound ((summable_cosWeight hRH).mul_left 2)

private theorem state_deriv_coeff (q : XiZeroCopy) :
    ccmPrimeDeficitBohrStateCoeff q * ((zeroOrdinate q : ℂ) * Complex.I) =
      (cosWeight q : ℂ) - ccmPrimeDeficitBohrStateCoeff q / 2 := by
  have h : ccmPrimeDeficitBohrStateCoeff q *
      (1 / 2 + (zeroOrdinate q : ℂ) * Complex.I) = (cosWeight q : ℂ) :=
    div_mul_cancel₀ _ (state_den_ne q)
  linear_combination h

private theorem state_deriv_coeff_bound (q : XiZeroCopy) :
    ‖ccmPrimeDeficitBohrStateCoeff q * ((zeroOrdinate q : ℂ) * Complex.I)‖ ≤
      2 * cosWeight q := by
  rw [state_deriv_coeff]
  calc
    _ ≤ ‖(cosWeight q : ℂ)‖ + ‖ccmPrimeDeficitBohrStateCoeff q / 2‖ := norm_sub_le _ _
    _ ≤ cosWeight q + (2 * cosWeight q) / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cosWeight_pos q)]
      have ht : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [ht]
      nlinarith [state_coeff_bound q]
    _ = _ := by ring

private theorem deriv_character (g t : ℝ) :
    HasDerivAt (expChar g) (((g : ℂ) * Complex.I) * expChar g t) t := by
  convert! (((Complex.hasDerivAt_ofReal t).const_mul (g : ℂ)).mul_const Complex.I).cexp using 1
  · ext x
    simp only [expChar, Complex.ofReal_mul]
  · simp only [expChar, mul_one, Complex.ofReal_mul]
    rw [show (g : ℂ) * (t : ℂ) * Complex.I = (g : ℂ) * Complex.I * (t : ℂ) by ring]
    ring

/-- The complete state solves the stable flux equation under RH. -/
theorem hasDerivAt_ccmPrimeDeficitBohrState (hRH : RiemannHypothesis) (t : ℝ) :
    HasDerivAt ccmPrimeDeficitBohrState
      (weilLagFunction t - ccmPrimeDeficitBohrState t / 2) t := by
  have hs := summable_state_coeff hRH
  have hd := hasDerivAt_tsum ((summable_cosWeight hRH).mul_left 2)
    (fun q x => (deriv_character (zeroOrdinate q) x).const_mul
      (ccmPrimeDeficitBohrStateCoeff q))
    (fun q x => by
      rw [← mul_assoc, norm_mul, norm_expChar, mul_one]
      exact state_deriv_coeff_bound q)
    (summable_expSeries hs zeroOrdinate 0) t
  convert! hd using 1
  rw [ccmPrimeDeficitBohrState, expSeriesCarrier,
    weilLagFunction_eq_expSeriesCarrier hRH, expSeriesCarrier,
    ← tsum_div_const,
    ← (summable_expSeries (summable_norm_cosWeight hRH) zeroOrdinate t).tsum_sub
      ((summable_expSeries hs zeroOrdinate t).div_const 2)]
  apply tsum_congr
  intro q
  rw [← mul_assoc, state_deriv_coeff]
  ring

private theorem state_continuous (hRH : RiemannHypothesis) :
    Continuous ccmPrimeDeficitBohrState :=
  continuous_expSeriesCarrier (summable_state_coeff hRH) _

private theorem state_ap (hRH : RiemannHypothesis) :
    HTGeometry.IsBohrAlmostPeriodic ccmPrimeDeficitBohrState :=
  isBohrAlmostPeriodic_expSeriesCarrier (summable_state_coeff hRH) _

private theorem state_mean (hRH : RiemannHypothesis) :
    bohrMean ccmPrimeDeficitBohrState = 0 := by
  rw [bohrMean_eq_bohrCoefficient_zero]
  exact bohrCoefficient_expSeriesCarrier_of_ne (summable_state_coeff hRH)
    (fun q => zeroOrdinate_ne_zero hRH q)


private theorem ap_re {f : ℝ → ℂ} (hf : HTGeometry.IsBohrAlmostPeriodic f) :
    HTGeometry.IsBohrAlmostPeriodic (fun t => (f t).re) := by
  intro ε hε
  obtain ⟨L, hL, hτ⟩ := hf ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hτ a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hb : ‖(f (x + τ)).re - (f x).re‖ ≤ ‖f (x + τ) - f x‖ := by
    simpa only [Real.norm_eq_abs, Complex.sub_re] using
      (Complex.abs_re_le_norm (f (x + τ) - f x))
  exact hb.trans (hτ x)

private theorem mean_re_zero {f : ℝ → ℂ} (hc : Continuous f)
    (ha : HTGeometry.IsBohrAlmostPeriodic f) (hm : bohrMean f = 0) :
    bohrMean (fun t => ((f t).re : ℂ)) = 0 := by
  have he : (fun t => ((f t).re : ℂ)) = fun t => (1 / 2 : ℂ) * (f t + conj (f t)) := by
    funext t
    apply Complex.ext <;> simp
    ring
  rw [he, bohrMean_const_mul (f := fun t => f t + conj (f t)) _ (hc.add (Complex.continuous_conj.comp hc))
      (isBohrAlmostPeriodic_add hc ha (Complex.continuous_conj.comp hc)
        (isBohrAlmostPeriodic_conj ha)),
    bohrMean_add (g := fun t => conj (f t)) hc ha (Complex.continuous_conj.comp hc) (isBohrAlmostPeriodic_conj ha),
    bohrMean_conj hc ha, hm]
  simp

private theorem incoming_continuous (hRH : RiemannHypothesis) :
    Continuous ccmPrimeDeficitBohrIncoming :=
  (Complex.continuous_re.comp (state_continuous hRH)).sub
    (Complex.continuous_re.comp (continuous_weilLagFunction hRH))

private theorem incoming_ap (hRH : RiemannHypothesis) :
    HTGeometry.IsBohrAlmostPeriodic ccmPrimeDeficitBohrIncoming :=
  isBohrAlmostPeriodic_sub (Complex.continuous_re.comp (state_continuous hRH))
    (ap_re (state_ap hRH)) (Complex.continuous_re.comp (continuous_weilLagFunction hRH))
    (isBohrAlmostPeriodic_weilLagFunctionReal hRH)

private theorem incoming_mean (hRH : RiemannHypothesis) :
    bohrMean (fun t => (ccmPrimeDeficitBohrIncoming t : ℂ)) = 0 := by
  have he : (fun t => (ccmPrimeDeficitBohrIncoming t : ℂ)) =
      fun t => ((ccmPrimeDeficitBohrState t).re : ℂ) - weilLagFunction t := by
    ext t
    rw [ccmPrimeDeficitBohrIncoming, Complex.ofReal_sub, weilLagFunction_eq_ofReal]
  rw [he, bohrMean_sub (f := fun t => ((ccmPrimeDeficitBohrState t).re : ℂ))
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (state_continuous hRH)))
      (isBohrAlmostPeriodic_coe_ofReal (ap_re (state_ap hRH)))
      (continuous_weilLagFunction hRH) (isBohrAlmostPeriodic_weilLagFunction hRH),
    mean_re_zero (state_continuous hRH) (state_ap hRH) (state_mean hRH),
    bohrMean_weilLagFunction hRH, sub_zero]

private theorem state_coeff_re (q : XiZeroCopy) :
    (ccmPrimeDeficitBohrStateCoeff q).re = cosWeight q ^ 2 / 2 := by
  have hr : ((1 / 2 : ℂ) + (zeroOrdinate q : ℂ) * Complex.I).re = (1 / 2 : ℝ) := by simp
  have hi : ((1 / 2 : ℂ) + (zeroOrdinate q : ℂ) * Complex.I).im = zeroOrdinate q := by simp
  have hn : Complex.normSq ((1 / 2 : ℂ) + (zeroOrdinate q : ℂ) * Complex.I) =
      1 / 4 + zeroOrdinate q ^ 2 := by
    rw [Complex.normSq_apply, hr, hi]
    ring
  rw [ccmPrimeDeficitBohrStateCoeff, Complex.div_re, hr, hi, hn,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  unfold cosWeight
  ring

/-- The actual source gap, not a numerical zero check, fixes a negative value of the model. -/
theorem ccmPrimeDeficitBohrIncoming_zero_neg (hRH : RiemannHypothesis) :
    ccmPrimeDeficitBohrIncoming 0 < 0 := by
  have hw (q : XiZeroCopy) : cosWeight q ≤ 1 := by
    have hg := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    unfold cosWeight zeroOrdinate
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hr : (ccmPrimeDeficitBohrState 0).re =
      ∑' q : XiZeroCopy, cosWeight q ^ 2 / 2 := by
    unfold ccmPrimeDeficitBohrState expSeriesCarrier
    rw [Complex.re_tsum (summable_expSeries (summable_state_coeff hRH) zeroOrdinate 0)]
    apply tsum_congr
    intro q
    simp only [expChar, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    exact state_coeff_re q
  have hs : Summable (fun q : XiZeroCopy => cosWeight q ^ 2 / 2) := by
    apply Summable.of_nonneg_of_le (fun q => by positivity) _ (summable_cosWeight hRH)
    intro q
    have hp := cosWeight_pos q
    nlinarith [hw q]
  have hb : (ccmPrimeDeficitBohrState 0).re ≤ poleSharpConstant / 2 := by
    rw [hr, ← tsum_cosWeight hRH, ← tsum_div_const]
    apply hs.tsum_le_tsum _ ((summable_cosWeight hRH).div_const 2)
    intro q
    have hp := cosWeight_pos q
    nlinarith [hw q]
  have hl : weilLagFunctionReal 0 = poleSharpConstant := by
    unfold weilLagFunctionReal
    rw [weilLagFunction_zero, Complex.ofReal_re]
  unfold ccmPrimeDeficitBohrIncoming
  rw [hl]
  linarith [poleSharpConstant_pos]


private theorem exp_half_decay :
    Tendsto (fun T : ℝ => Real.exp (-T / 2)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  simpa only [neg_div, Function.comp_def, id_eq] using h

private theorem linear_exp_half_decay :
    Tendsto (fun T : ℝ => T * Real.exp (-T / 2)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).const_mul 2
  norm_num only [mul_zero, pow_one, Function.comp_def, id_eq] at h
  refine h.congr fun T => ?_
  rw [neg_div]
  ring

private theorem outgoing_lag_decay :
    Tendsto (fun T => ccmPrimeDeficitOutgoing T - weilLagFunctionReal T) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _
    (show Tendsto (fun T => Real.exp (-T / 2) * (|Real.log (2 * Real.pi)| + 1))
      atTop (𝓝 0) by simpa using exp_half_decay.mul_const (|Real.log (2 * Real.pi)| + 1))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact abs_ccmPrimeDeficitOutgoing_sub_weilLag hT

private theorem state_real_deriv (hRH : RiemannHypothesis) (t : ℝ) :
    HasDerivAt (fun x => (ccmPrimeDeficitBohrState x).re)
      (weilLagFunctionReal t - (ccmPrimeDeficitBohrState t).re / 2) t := by
  simpa only [Complex.reCLM_apply, Function.comp_def, Complex.sub_re,
    Complex.div_ofNat_re, weilLagFunctionReal] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_ccmPrimeDeficitBohrState hRH t)

private theorem state_difference_decay (hRH : RiemannHypothesis) :
    Tendsto (fun T => ccmPrimeDeficitFluxState T - (ccmPrimeDeficitBohrState T).re)
      atTop (𝓝 0) := by
  let R : ℝ → ℝ := fun t => Real.exp (t / 2) *
    (ccmPrimeDeficitFluxState t - (ccmPrimeDeficitBohrState t).re)
  let C : ℝ := |Real.log (2 * Real.pi)| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd (t : ℝ) : HasDerivAt R
      (Real.exp (t / 2) * (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t)) t := by
    convert! (((hasDerivAt_id t).div_const 2).exp).mul
      ((hasDerivAt_ccmPrimeDeficitFluxState t).sub (state_real_deriv hRH t)) using 1
    dsimp only [ccmPrimeDeficitOutgoing, id_eq, Pi.sub_apply]
    ring
  have hbd (t : ℝ) (ht : 1 ≤ t) :
      ‖Real.exp (t / 2) * (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t)‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_left
      (abs_ccmPrimeDeficitOutgoing_sub_weilLag (by linarith : 0 < t))
      (Real.exp_pos (t / 2)).le
    have he : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
      rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
    simpa only [← mul_assoc, he, one_mul] using h
  have hR (T : ℝ) (hT : 1 ≤ T) : |R T| ≤ |R 1| + C * T := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t (_ht : t ∈ Icc (1 : ℝ) T) => (hd t).hasDerivWithinAt)
      (fun t ht => hbd t ht.1) (convex_Icc 1 T)
      (show (1 : ℝ) ∈ Icc 1 T from ⟨le_rfl, hT⟩)
      (show T ∈ Icc 1 T from ⟨hT, le_rfl⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T - 1)] at h
    have ha := abs_add_le (R T - R 1) (R 1)
    rw [sub_add_cancel] at ha
    nlinarith
  apply squeeze_zero_norm' _
    (show Tendsto (fun T => |R 1| * Real.exp (-T / 2) + C * (T * Real.exp (-T / 2)))
      atTop (𝓝 0) by
        simpa using (exp_half_decay.const_mul |R 1|).add (linear_exp_half_decay.const_mul C))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have he : ccmPrimeDeficitFluxState T - (ccmPrimeDeficitBohrState T).re =
      Real.exp (-T / 2) * R T := by
    dsimp [R]
    rw [← mul_assoc, ← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero, one_mul]
  rw [he, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-T / 2) * (|R 1| + C * T) :=
      mul_le_mul_of_nonneg_left (hR T hT) (Real.exp_pos _).le
    _ = _ := by ring

/-- The literal arithmetic incoming flux approaches the complete signed Bohr model. -/
theorem tendsto_ccmPrimeDeficitIncoming_sub_bohr (hRH : RiemannHypothesis) :
    Tendsto (fun T => ccmPrimeDeficitIncoming T - ccmPrimeDeficitBohrIncoming T)
      atTop (𝓝 0) := by
  have h := (state_difference_decay hRH).sub outgoing_lag_decay
  simp only [sub_zero] at h
  convert! h using 1
  ext T
  dsimp [ccmPrimeDeficitBohrIncoming, ccmPrimeDeficitOutgoing]
  ring


private theorem incoming_model_pos (hRH : RiemannHypothesis) :
    ∃ t : ℝ, 0 < ccmPrimeDeficitBohrIncoming t := by
  by_contra hn
  push Not at hn
  let f : ℝ → ℂ := fun t => (ccmPrimeDeficitBohrIncoming t : ℂ)
  have hc : Continuous f := Complex.continuous_ofReal.comp (incoming_continuous hRH)
  have ha : HTGeometry.IsBohrAlmostPeriodic f :=
    isBohrAlmostPeriodic_coe_ofReal (incoming_ap hRH)
  have hm : bohrMean (fun t => (-1 : ℂ) * f t) = 0 := by
    rw [bohrMean_const_mul _ hc ha]
    change (-1 : ℂ) * bohrMean (fun t => (ccmPrimeDeficitBohrIncoming t : ℂ)) = 0
    rw [incoming_mean hRH, mul_zero]
  have hz := eq_zero_of_bohrMean_eq_zero_of_nonneg (continuous_const.mul hc)
    (isBohrAlmostPeriodic_const_mul (-1) ha)
    (fun t => by simpa [f] using neg_nonneg.mpr (hn t))
    (fun t => by simp [f]) hm 0
  have hz' : ccmPrimeDeficitBohrIncoming 0 = 0 := by
    have := congrArg Complex.re hz
    simpa [f] using this
  exact (ne_of_lt (ccmPrimeDeficitBohrIncoming_zero_neg hRH)) hz'

private theorem frequently_incoming_near_model (hRH : RiemannHypothesis)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ T : ℝ in atTop, |ccmPrimeDeficitIncoming T - ccmPrimeDeficitBohrIncoming t| < ε := by
  obtain ⟨L, _, hp⟩ := incoming_ap hRH (ε / 3) (by positivity)
  have hs := (tendsto_ccmPrimeDeficitIncoming_sub_bohr hRH).abs.eventually_lt_const
    (show |(0 : ℝ)| < ε / 3 by rw [abs_zero]; positivity)
  obtain ⟨A, hA⟩ := eventually_atTop.mp hs
  apply frequently_atTop.mpr
  intro M
  obtain ⟨τ, hτ, hb⟩ := hp (max A M - t)
  have hAT : A ≤ t + τ := by linarith [hτ.1, le_max_left A M]
  have hMT : M ≤ t + τ := by linarith [hτ.1, le_max_right A M]
  refine ⟨t + τ, hMT, ?_⟩
  have h1 := hA (t + τ) hAT
  have h2 := hb t
  rw [Real.norm_eq_abs] at h2
  have h3 := abs_add_le
    (ccmPrimeDeficitIncoming (t + τ) - ccmPrimeDeficitBohrIncoming (t + τ))
    (ccmPrimeDeficitBohrIncoming (t + τ) - ccmPrimeDeficitBohrIncoming t)
  rw [sub_add_sub_cancel] at h3
  linarith

private theorem incoming_omega_of_rh (hRH : RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ (∃ᶠ T : ℝ in atTop, c < ccmPrimeDeficitIncoming T) ∧
      ∃ᶠ T : ℝ in atTop, ccmPrimeDeficitIncoming T < -c := by
  obtain ⟨t, ht⟩ := incoming_model_pos hRH
  have hn := ccmPrimeDeficitBohrIncoming_zero_neg hRH
  let c : ℝ := min (ccmPrimeDeficitBohrIncoming t / 3)
    (-ccmPrimeDeficitBohrIncoming 0 / 3)
  have hc : 0 < c := lt_min (by linarith) (by linarith)
  refine ⟨c, hc, ?_, ?_⟩
  · apply (frequently_incoming_near_model hRH t hc).mono
    intro T hT
    have hb := (abs_lt.mp hT).1
    have hct : c ≤ ccmPrimeDeficitBohrIncoming t / 3 := min_le_left _ _
    linarith
  · apply (frequently_incoming_near_model hRH 0 hc).mono
    intro T hT
    have hb := (abs_lt.mp hT).2
    have hct : c ≤ -ccmPrimeDeficitBohrIncoming 0 / 3 := min_le_right _ _
    linarith

private theorem rh_of_incoming_eventual_oneSided {ε c : ℝ}
    (hε : ε = 1 ∨ ε = -1)
    (h : ∀ᶠ T : ℝ in atTop, -c ≤ ε * ccmPrimeDeficitIncoming T) :
    RiemannHypothesis := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp h
  let M := max A 0
  have hM : 0 ≤ M := le_max_right _ _
  obtain ⟨t, _, ht⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_isMaxOn
    ⟨0, le_rfl, hM⟩ continuous_ccmPrimeDeficitIncoming.abs.continuousOn
  let B := max (max c 0) |ccmPrimeDeficitIncoming t|
  have hB : 0 ≤ B := (le_max_right c 0).trans (le_max_left _ _)
  have hcB : c ≤ B := (le_max_left c 0).trans (le_max_left _ _)
  have hglobal (T : ℝ) (hT : 0 ≤ T) : -B ≤ ε * ccmPrimeDeficitIncoming T := by
    by_cases hMT : M ≤ T
    · have hh := hA T ((le_max_left A 0).trans hMT)
      linarith
    · have hh : |ccmPrimeDeficitIncoming T| ≤ B :=
        (ht ⟨hT, (not_le.mp hMT).le⟩).trans (le_max_right _ _)
      rcases hε with rfl | rfl <;> simp only [one_mul, neg_mul, one_mul]
      · exact (abs_le.mp hh).1
      · linarith [(abs_le.mp hh).2]
  apply riemannHypothesis_of_logChebyshevDeficitPrimitive_oneSided hε (B := B)
  intro T hT
  have hg := hglobal T hT
  change -B ≤ ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T) at hg
  nlinarith

/-- Unconditionally, the actual critical prime deficit has two nonvanishing signs cofinally. -/
theorem ccmPrimeDeficitIncoming_omega_pm :
    ∃ c : ℝ, 0 < c ∧ (∃ᶠ T : ℝ in atTop, c < ccmPrimeDeficitIncoming T) ∧
      ∃ᶠ T : ℝ in atTop, ccmPrimeDeficitIncoming T < -c := by
  by_cases hRH : RiemannHypothesis
  · exact incoming_omega_of_rh hRH
  refine ⟨1, zero_lt_one, ?_, ?_⟩
  · by_contra hn
    rw [not_frequently] at hn
    apply hRH
    apply rh_of_incoming_eventual_oneSided (ε := -1) (c := 1) (Or.inr rfl)
    filter_upwards [hn] with T hT
    simp only [neg_mul, one_mul]
    linarith
  · by_contra hn
    rw [not_frequently] at hn
    apply hRH
    apply rh_of_incoming_eventual_oneSided (ε := 1) (c := 1) (Or.inl rfl)
    filter_upwards [hn] with T hT
    simpa using not_lt.mp hT

/-- The complete signed quantile action oscillates; both terminal orientations remain present. -/
theorem ccmActualTimeExponentialRampAction_omega_pm :
    ∃ c : ℝ, 0 < c ∧
      (∃ᶠ T : ℝ in atTop, c < ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊ + 1)
        (ccmNormalizedExponentialRampTest T)) ∧
      ∃ᶠ T : ℝ in atTop, ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊ + 1)
        (ccmNormalizedExponentialRampTest T) < -c := by
  obtain ⟨c, hc, hp, hn⟩ := ccmPrimeDeficitIncoming_omega_pm
  have hs := linear_exp_half_decay.abs.eventually_lt_const
    (show |(0 : ℝ)| < c / 2 by rw [abs_zero]; positivity)
  have he (T : ℝ) (hT : 0 ≤ T) :
      ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊ + 1) (ccmNormalizedExponentialRampTest T) =
        ccmPrimeDeficitIncoming T - T * Real.exp (-T / 2) := by
    have h := ccmActualTimeExponentialRampAction_eq_normalizedDeficit (⟨T, hT⟩ : NNReal)
    change ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊ + 1) (ccmNormalizedExponentialRampTest T) =
      Real.exp (-T / 2) * (ccmLogChebyshevDeficitPrimitive T - T) at h
    rw [h, ccmPrimeDeficitIncoming]
    ring
  refine ⟨c / 2, by positivity, ?_, ?_⟩
  · apply ((hp.and_eventually hs).and_eventually (eventually_ge_atTop (0 : ℝ))).mono
    intro T hT
    rw [he T hT.2]
    linarith [(abs_lt.mp hT.1.2).2, hT.1.1]
  · apply ((hn.and_eventually hs).and_eventually (eventually_ge_atTop (0 : ℝ))).mono
    intro T hT
    rw [he T hT.2]
    linarith [(abs_lt.mp hT.1.2).1, hT.1.1]


/-- The stable flux map preserves the modulus of each full-divisor lag coefficient. -/
theorem norm_ccmPrimeDeficitBohrIncoming_coeff (q : XiZeroCopy) :
    ‖ccmPrimeDeficitBohrStateCoeff q - (cosWeight q : ℂ)‖ = cosWeight q := by
  let d : ℂ := 1 / 2 + (zeroOrdinate q : ℂ) * Complex.I
  have hd : d ≠ 0 := state_den_ne q
  have hc : conj d = 1 - d := by
    dsimp [d]
    apply Complex.ext <;> simp
    ring
  have he : ccmPrimeDeficitBohrStateCoeff q - (cosWeight q : ℂ) =
      (cosWeight q : ℂ) * (conj d / d) := by
    change (cosWeight q : ℂ) / d - (cosWeight q : ℂ) = _
    rw [hc, ← mul_div_assoc, mul_sub, mul_one, sub_div, mul_div_cancel_right₀ _ hd]
  rw [he, norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hd),
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cosWeight_pos q)]

end RHTower
