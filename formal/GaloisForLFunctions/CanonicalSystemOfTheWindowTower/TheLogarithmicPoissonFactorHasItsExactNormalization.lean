import GaloisForLFunctions.RHTower.LogSineClockTransform
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Exact normalization of the logarithmic Poisson factor

For Ψ(t)=1+(1/2)log(1+t²), the positive Poisson factor is defined by the
literal half-line logarithmic integral. In logarithmic frequency its
normalized logarithm is a sech average of translated symbol differences.
Derivative bounds provide an integrable majorant and a vanishing pointwise
limit, giving κ(s)/sqrt(log s) tending to one.
-/

open MeasureTheory Set Filter Topology
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- The multiplier of the strictly positive reference operator `1+(1/2)log(1-D²)`. -/
def positiveLogarithmicSymbol (t : ℝ) : ℝ := 1 + (1 / 2) * Real.log (1 + t ^ 2)

/-- The logarithm of the reference symbol in logarithmic frequency. -/
def logReferenceLogSymbol (w : ℝ) : ℝ :=
  Real.log (2 + Real.log (1 + Real.exp (2 * w))) - Real.log 2

private def logReferenceLogSymbolDeriv (w : ℝ) : ℝ :=
  2 * Real.exp (2 * w) /
    ((1 + Real.exp (2 * w)) * (2 + Real.log (1 + Real.exp (2 * w))))

private theorem logReferenceLogSymbol_inner_pos (w : ℝ) :
    0 < 2 + Real.log (1 + Real.exp (2 * w)) := by
  have h := Real.log_pos (show 1 < 1 + Real.exp (2 * w) by
    linarith only [Real.exp_pos (2 * w)])
  linarith only [h]

private theorem hasDerivAt_logReferenceLogSymbol (w : ℝ) :
    HasDerivAt logReferenceLogSymbol (logReferenceLogSymbolDeriv w) w := by
  have he := ((hasDerivAt_id w).const_mul 2).exp
  have hl := (he.const_add 1).log (by positivity)
  have hll := (hl.const_add 2).log (logReferenceLogSymbol_inner_pos w).ne'
  have hbase : HasDerivAt logReferenceLogSymbol
      ((Real.exp (2 * w) * 2 / (1 + Real.exp (2 * w))) /
        (2 + Real.log (1 + Real.exp (2 * w)))) w := by
    simpa only [id_eq, mul_one, logReferenceLogSymbol] using! hll.sub_const (Real.log 2)
  have hc : logReferenceLogSymbolDeriv w =
      (Real.exp (2 * w) * 2 / (1 + Real.exp (2 * w))) /
        (2 + Real.log (1 + Real.exp (2 * w))) := by
    unfold logReferenceLogSymbolDeriv
    rw [div_div]
    ring
  rw [hc]
  exact hbase

private theorem logReferenceLogSymbolDeriv_nonneg (w : ℝ) :
    0 ≤ logReferenceLogSymbolDeriv w := by
  unfold logReferenceLogSymbolDeriv
  exact div_nonneg (by positivity)
    (mul_nonneg (by positivity) (logReferenceLogSymbol_inner_pos w).le)

private theorem logReferenceLogSymbolDeriv_le_two (w : ℝ) :
    logReferenceLogSymbolDeriv w ≤ 2 := by
  have hp : 0 < 1 + Real.exp (2 * w) := by positivity
  have hl := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos hp) hp.le
  have he : (1 + Real.exp (2 * w)) * (1 - (1 + Real.exp (2 * w))⁻¹) =
      Real.exp (2 * w) := by field_simp; ring
  rw [he] at hl
  unfold logReferenceLogSymbolDeriv
  apply (div_le_iff₀ (mul_pos hp (logReferenceLogSymbol_inner_pos w))).mpr
  nlinarith only [hl, Real.exp_pos (2 * w)]

private theorem logReferenceLogSymbolDeriv_le_inv {w : ℝ} (hw : 0 < w) :
    logReferenceLogSymbolDeriv w ≤ w⁻¹ := by
  have hp : 0 < 1 + Real.exp (2 * w) := by positivity
  have hl : 2 * w ≤ Real.log (1 + Real.exp (2 * w)) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (2 * w))
        (show Real.exp (2 * w) ≤ 1 + Real.exp (2 * w) by linarith)
  have hm := mul_le_mul_of_nonneg_left hl hp.le
  unfold logReferenceLogSymbolDeriv
  apply (div_le_iff₀ (mul_pos hp (logReferenceLogSymbol_inner_pos w))).mpr
  rw [inv_mul_eq_div, le_div_iff₀ hw]
  nlinarith only [hm, hw, Real.exp_pos (2 * w)]

/-- A common Lipschitz bound controls every translated logarithmic symbol. -/
theorem logReferenceLogSymbol_shift_bound (w u : ℝ) :
    |logReferenceLogSymbol (w + u) - logReferenceLogSymbol w| ≤ 2 * |u| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (univ : Set ℝ)) =>
      (hasDerivAt_logReferenceLogSymbol x).hasDerivWithinAt)
    (fun x (_ : x ∈ (univ : Set ℝ)) => by
      rw [Real.norm_of_nonneg (logReferenceLogSymbolDeriv_nonneg x)]
      exact logReferenceLogSymbolDeriv_le_two x)
    convex_univ (mem_univ w) (mem_univ (w + u))
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using h

private theorem logReferenceLogSymbol_shift_decay {w : ℝ} (u : ℝ) (hw : |u| < w) :
    |logReferenceLogSymbol (w + u) - logReferenceLogSymbol w| ≤
      (w - |u|)⁻¹ * |u| := by
  have hc : 0 < w - |u| := sub_pos.mpr hw
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ Ici (w - |u|)) =>
      (hasDerivAt_logReferenceLogSymbol x).hasDerivWithinAt)
    (fun x (hx : x ∈ Ici (w - |u|)) => by
      rw [Real.norm_of_nonneg (logReferenceLogSymbolDeriv_nonneg x)]
      exact (logReferenceLogSymbolDeriv_le_inv (hc.trans_le hx)).trans
        (inv_anti₀ hc hx))
    (convex_Ici _) (show w ∈ Ici (w - |u|) by
      change w - |u| ≤ w
      exact sub_le_self _ (abs_nonneg _))
    (show w + u ∈ Ici (w - |u|) by
      change w - |u| ≤ w + u
      linarith only [neg_abs_le u])
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using h

/-- Fixed logarithmic frequency shifts become negligible at high frequency. -/
theorem tendsto_logReferenceLogSymbol_shift (u : ℝ) :
    Tendsto (fun w => logReferenceLogSymbol (w + u) - logReferenceLogSymbol w)
      atTop (nhds 0) := by
  have hlim : Tendsto (fun w : ℝ => (w - |u|)⁻¹ * |u|) atTop (nhds 0) := by
    have ht : Tendsto (fun w : ℝ => w - |u|) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using
        tendsto_atTop_add_const_right atTop (-|u|) tendsto_id
    simpa only [zero_mul, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp ht).mul_const |u|
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop |u|] with w hw
  simpa only [Real.norm_eq_abs] using logReferenceLogSymbol_shift_decay u hw

/-- The translated logarithmic remainder has vanishing Poisson average. -/
theorem tendsto_logReferenceLogSymbol_sech_average :
    Tendsto (fun w : ℝ => ∫ u : ℝ,
      (logReferenceLogSymbol (w + u) - logReferenceLogSymbol w) / Real.cosh u)
      atTop (nhds 0) := by
  have hdom : Integrable (fun u : ℝ => 2 * |u| / Real.cosh u) := by
    simpa only [pow_one, mul_div_assoc] using
      (RHTower.integrable_logSineSech_abs_pow 1).const_mul 2
  have hcont : Continuous logReferenceLogSymbol :=
    continuous_iff_continuousAt.mpr fun w =>
      (hasDerivAt_logReferenceLogSymbol w).continuousAt
  have h : Tendsto (fun w : ℝ => ∫ u : ℝ,
      (logReferenceLogSymbol (w + u) - logReferenceLogSymbol w) / Real.cosh u)
      atTop (nhds (∫ _ : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => 2 * |u| / Real.cosh u)
    · exact Filter.Eventually.of_forall fun w : ℝ =>
        ((hcont.comp (continuous_const.add continuous_id)).sub continuous_const |>.div
          Real.continuous_cosh (fun u => (Real.cosh_pos u).ne')).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun w : ℝ => Filter.Eventually.of_forall fun u => ?_
      change ‖(logReferenceLogSymbol (w + u) - logReferenceLogSymbol w) / Real.cosh u‖ ≤ _
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.cosh_pos u)]
      exact div_le_div_of_nonneg_right (logReferenceLogSymbol_shift_bound w u)
        (Real.cosh_pos u).le
    · exact hdom
    · exact Filter.Eventually.of_forall fun u => by
        simpa only [zero_div] using (tendsto_logReferenceLogSymbol_shift u).div_const
          (Real.cosh u)
  simpa only [integral_zero] using h


private theorem integral_logReference_sech :
    (∫ u : ℝ, 1 / Real.cosh u) = Real.pi := by
  have h := HTGeometry.integral_cexp_div_cosh (z := 0) (by simp)
  simp only [zero_mul, neg_zero, Complex.exp_zero, mul_zero, zero_div,
    Complex.cosh_zero, div_one] at h
  have hcast : (fun u : ℝ => (1 : ℂ) / (Real.cosh u : ℂ)) =
      fun u : ℝ => ((1 / Real.cosh u : ℝ) : ℂ) := by
    funext u
    simp only [Complex.ofReal_div, Complex.ofReal_one]
  rw [hcast, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

private theorem integrable_logReferenceLogSymbol_sech (w : ℝ) :
    Integrable (fun u : ℝ => logReferenceLogSymbol (w + u) / Real.cosh u) := by
  have hcont : Continuous logReferenceLogSymbol :=
    continuous_iff_continuousAt.mpr fun w =>
      (hasDerivAt_logReferenceLogSymbol w).continuousAt
  have hd : Integrable (fun u : ℝ =>
      (logReferenceLogSymbol (w + u) - logReferenceLogSymbol w) / Real.cosh u) := by
    apply ((RHTower.integrable_logSineSech_abs_pow 1).const_mul 2).mono'
    · exact ((hcont.comp (continuous_const.add continuous_id)).sub continuous_const |>.div
        Real.continuous_cosh (fun u => (Real.cosh_pos u).ne')).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.cosh_pos u), pow_one]
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (logReferenceLogSymbol_shift_bound w u)
          (Real.cosh_pos u).le
  have hc : Integrable (fun u : ℝ => logReferenceLogSymbol w / Real.cosh u) := by
    simpa only [pow_zero, mul_one_div] using
      (RHTower.integrable_logSineSech_abs_pow 0).const_mul (logReferenceLogSymbol w)
  refine (hd.add hc).congr ?_
  filter_upwards with u
  change (logReferenceLogSymbol (w + u) - logReferenceLogSymbol w) / Real.cosh u +
    logReferenceLogSymbol w / Real.cosh u = _
  ring

/-- The positive Poisson factor of the shifted logarithmic symbol. -/
def logReferenceFactor (s : ℝ) : ℝ :=
  Real.exp ((1 / (2 * Real.pi)) * ∫ u : ℝ,
    logReferenceLogSymbol (Real.log s + u) / Real.cosh u)

theorem logReferenceFactor_pos (s : ℝ) : 0 < logReferenceFactor s := Real.exp_pos _

private theorem logReferenceFactor_normalized (s : ℝ) :
    logReferenceFactor s / Real.exp (logReferenceLogSymbol (Real.log s) / 2) =
      Real.exp ((1 / (2 * Real.pi)) * ∫ u : ℝ,
        (logReferenceLogSymbol (Real.log s + u) - logReferenceLogSymbol (Real.log s)) /
          Real.cosh u) := by
  have hc : Integrable (fun u : ℝ => logReferenceLogSymbol (Real.log s) / Real.cosh u) := by
    simpa only [pow_zero, mul_one_div] using
      (RHTower.integrable_logSineSech_abs_pow 0).const_mul
        (logReferenceLogSymbol (Real.log s))
  have hd : (∫ u : ℝ,
      (logReferenceLogSymbol (Real.log s + u) - logReferenceLogSymbol (Real.log s)) /
        Real.cosh u) =
      (∫ u : ℝ, logReferenceLogSymbol (Real.log s + u) / Real.cosh u) -
        logReferenceLogSymbol (Real.log s) * Real.pi := by
    simp_rw [sub_div]
    rw [integral_sub (integrable_logReferenceLogSymbol_sech _) hc]
    congr 1
    have he : (fun u : ℝ => logReferenceLogSymbol (Real.log s) / Real.cosh u) =
        (fun u : ℝ => logReferenceLogSymbol (Real.log s) * (1 / Real.cosh u)) := by
      funext u
      ring
    rw [he]
    rw [integral_const_mul, integral_logReference_sech]
  rw [logReferenceFactor, ← Real.exp_sub, hd]
  congr 1
  field_simp [Real.pi_ne_zero]

/-- The exact factor agrees asymptotically with the square root of its symbol. -/
theorem tendsto_logReferenceFactor_normalized :
    Tendsto (fun s : ℝ => logReferenceFactor s /
      Real.exp (logReferenceLogSymbol (Real.log s) / 2)) atTop (nhds 1) := by
  have h : Tendsto (fun s : ℝ => Real.exp ((1 / (2 * Real.pi)) * ∫ u : ℝ,
      (logReferenceLogSymbol (Real.log s + u) - logReferenceLogSymbol (Real.log s)) /
        Real.cosh u)) atTop (nhds 1) := by
    simpa only [Function.comp_def, mul_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_logReferenceLogSymbol_sech_average.comp Real.tendsto_log_atTop).const_mul
          (1 / (2 * Real.pi)))
  exact h.congr' (Filter.Eventually.of_forall fun s =>
    (logReferenceFactor_normalized s).symm)

theorem logReferenceLogSymbol_eq_log (w : ℝ) :
    logReferenceLogSymbol w = Real.log (positiveLogarithmicSymbol (Real.exp w)) := by
  have hs : Real.exp w ^ 2 = Real.exp (2 * w) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  unfold positiveLogarithmicSymbol logReferenceLogSymbol
  rw [hs, show 1 + (1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * w)) =
      (1 / 2 : ℝ) * (2 + Real.log (1 + Real.exp (2 * w))) by ring,
    Real.log_mul (by norm_num) (logReferenceLogSymbol_inner_pos w).ne', hh]
  ring

theorem positiveLogarithmicSymbol_pos {s : ℝ} (hs : 0 < s) :
    0 < positiveLogarithmicSymbol s := by
  unfold positiveLogarithmicSymbol
  exact add_pos zero_lt_one
    (mul_pos (by norm_num) (Real.log_pos (by nlinarith only [sq_pos_of_pos hs])))

theorem exp_half_logReferenceLogSymbol {s : ℝ} (hs : 0 < s) :
    Real.exp (logReferenceLogSymbol (Real.log s) / 2) =
      Real.sqrt (positiveLogarithmicSymbol s) := by
  rw [logReferenceLogSymbol_eq_log, Real.exp_log hs]
  have hsq : Real.exp (Real.log (positiveLogarithmicSymbol s) / 2) ^ 2 =
      positiveLogarithmicSymbol s := by
    rw [pow_two, ← Real.exp_add,
      show Real.log (positiveLogarithmicSymbol s) / 2 +
        Real.log (positiveLogarithmicSymbol s) / 2 =
        Real.log (positiveLogarithmicSymbol s) by ring,
      Real.exp_log (positiveLogarithmicSymbol_pos hs)]
  have h := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (Real.exp_nonneg _)] at h

theorem tendsto_logReferenceFactor_div_sqrt_symbol :
    Tendsto (fun s : ℝ => logReferenceFactor s /
      Real.sqrt (positiveLogarithmicSymbol s)) atTop (nhds 1) := by
  apply tendsto_logReferenceFactor_normalized.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [exp_half_logReferenceLogSymbol hs]

theorem tendsto_positiveLogarithmicSymbol_div_log :
    Tendsto (fun s : ℝ => positiveLogarithmicSymbol s / Real.log s)
      atTop (nhds 1) := by
  have hv : Tendsto (fun s : ℝ => 1 + (s⁻¹) ^ 2) atTop (nhds 1) := by
    have hi : Tendsto (fun s : ℝ => s⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add (hi.pow 2)
  have hl : Tendsto (fun s : ℝ => Real.log (1 + (s⁻¹) ^ 2)) atTop (nhds 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hv
  have hn : Tendsto (fun s : ℝ => 1 + (1 / 2 : ℝ) *
      Real.log (1 + (s⁻¹) ^ 2)) atTop (nhds 1) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (hl.const_mul (1 / 2 : ℝ))
  have hlim : Tendsto (fun s : ℝ => 1 +
      (1 + (1 / 2 : ℝ) * Real.log (1 + (s⁻¹) ^ 2)) / Real.log s)
      atTop (nhds 1) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (hn.div_atTop Real.tendsto_log_atTop)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hf : 1 + s ^ 2 = s ^ 2 * (1 + (s⁻¹) ^ 2) := by
    field_simp [hs0.ne']
    ring
  have hlog : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  unfold positiveLogarithmicSymbol
  rw [hf, Real.log_mul (pow_ne_zero 2 hs0.ne') (by positivity), Real.log_pow]
  field_simp [hlog]
  ring

theorem tendsto_logReferenceFactor_div_sqrt_log :
    Tendsto (fun s : ℝ => logReferenceFactor s / Real.sqrt (Real.log s))
      atTop (nhds 1) := by
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt (positiveLogarithmicSymbol s) /
      Real.sqrt (Real.log s)) atTop (nhds 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      tendsto_positiveLogarithmicSymbol_div_log
    simp only [Real.sqrt_one] at h
    change Tendsto (fun s : ℝ => Real.sqrt (positiveLogarithmicSymbol s / Real.log s))
      atTop (nhds 1) at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [Real.sqrt_div (positiveLogarithmicSymbol_pos hs).le]
  have h := tendsto_logReferenceFactor_div_sqrt_symbol.mul hsqrt
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  have hpos := Real.sqrt_pos.mpr
    (positiveLogarithmicSymbol_pos (zero_lt_one.trans hs))
  field_simp [hpos.ne', (Real.sqrt_pos.mpr (Real.log_pos hs)).ne']

/-- The logarithmic coordinate formula is the literal positive-half-line Poisson factor. -/
theorem logReferenceFactor_eq_poisson {s : ℝ} (hs : 0 < s) :
    logReferenceFactor s = Real.exp ((1 / Real.pi) *
      ∫ t in Ioi (0 : ℝ), s * Real.log (positiveLogarithmicSymbol t) / (s ^ 2 + t ^ 2)) := by
  let f : ℝ → ℝ := fun t => s * Real.log (positiveLogarithmicSymbol t) / (s ^ 2 + t ^ 2)
  have hi : Set.InjOn (fun u : ℝ => s * Real.exp u) univ := by
    intro u _ v _ huv
    exact Real.exp_injective (mul_left_cancel₀ hs.ne' huv)
  have hd (u : ℝ) (_ : u ∈ (univ : Set ℝ)) :
      HasDerivWithinAt (fun u : ℝ => s * Real.exp u) (s * Real.exp u) univ u :=
    ((Real.hasDerivAt_exp u).const_mul s).hasDerivWithinAt
  have him : (fun u : ℝ => s * Real.exp u) '' univ = Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨u, _, rfl⟩
      exact mul_pos hs (Real.exp_pos u)
    · intro ht
      refine ⟨Real.log (t / s), mem_univ _, ?_⟩
      change s * Real.exp (Real.log (t / s)) = t
      rw [Real.exp_log (div_pos ht hs)]
      field_simp
  have hchange := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hi f
  rw [him, setIntegral_univ] at hchange
  have hpoint (u : ℝ) : |s * Real.exp u| • f (s * Real.exp u) =
      (1 / 2 : ℝ) * (logReferenceLogSymbol (Real.log s + u) / Real.cosh u) := by
    rw [logReferenceLogSymbol_eq_log, Real.exp_add, Real.exp_log hs,
      abs_of_pos (mul_pos hs (Real.exp_pos u)), smul_eq_mul]
    have he : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
    have hden : s ^ 2 + (s * Real.exp u) ^ 2 ≠ 0 := by positivity
    dsimp only [f]
    conv_rhs => rw [← mul_div_assoc]
    apply (eq_div_iff hc).mpr
    rw [Real.cosh_eq]
    field_simp [hden]
    nlinarith only [congrArg (fun r : ℝ =>
      Real.log (positiveLogarithmicSymbol (s * Real.exp u)) * r) he]
  rw [show (fun u => |s * Real.exp u| • f (s * Real.exp u)) =
      (fun u => (1 / 2 : ℝ) *
        (logReferenceLogSymbol (Real.log s + u) / Real.cosh u)) from funext hpoint,
    integral_const_mul] at hchange
  unfold logReferenceFactor
  change Real.exp _ = Real.exp ((1 / Real.pi) * ∫ t in Ioi (0 : ℝ), f t)
  rw [hchange]
  congr 1
  ring

#print axioms tendsto_logReferenceFactor_div_sqrt_log
#print axioms logReferenceFactor_eq_poisson

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
