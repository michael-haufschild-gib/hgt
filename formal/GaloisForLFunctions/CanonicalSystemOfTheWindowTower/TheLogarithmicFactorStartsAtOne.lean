import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicPoissonFactorHasItsExactNormalization

/-!
# The positive logarithmic factor at the origin

The symbol is at least one. Its logarithm increases with logarithmic frequency,
and its Poisson average therefore increases with the positive Laplace parameter.
An integrable sech majorant gives the exact limit one at zero.
-/

open MeasureTheory Set Filter Topology
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

theorem one_le_positiveLogarithmicSymbol (s : ℝ) :
    1 ≤ positiveLogarithmicSymbol s := by
  have h := Real.log_nonneg (show 1 ≤ 1 + s ^ 2 by nlinarith only [sq_nonneg s])
  unfold positiveLogarithmicSymbol
  linarith only [h]

theorem continuous_positiveLogarithmicSymbol : Continuous positiveLogarithmicSymbol := by
  unfold positiveLogarithmicSymbol
  exact continuous_const.add (continuous_const.mul
    ((continuous_const.add (continuous_id.pow 2)).log
      (fun s : ℝ => (show 0 < 1 + s ^ 2 by positivity).ne')))

theorem continuous_logReferenceLogSymbol : Continuous logReferenceLogSymbol := by
  rw [show logReferenceLogSymbol =
    (fun w => Real.log (positiveLogarithmicSymbol (Real.exp w))) from
      funext logReferenceLogSymbol_eq_log]
  exact (continuous_positiveLogarithmicSymbol.comp Real.continuous_exp).log
    (fun w => (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol _)).ne')

theorem logReferenceLogSymbol_nonneg (w : ℝ) : 0 ≤ logReferenceLogSymbol w := by
  rw [logReferenceLogSymbol_eq_log]
  exact Real.log_nonneg (one_le_positiveLogarithmicSymbol _)

theorem monotone_logReferenceLogSymbol : Monotone logReferenceLogSymbol := by
  intro w v hwv
  unfold logReferenceLogSymbol
  apply sub_le_sub_right
  apply Real.log_le_log
  · have h := Real.log_nonneg (show 1 ≤ 1 + Real.exp (2 * w) by
      linarith only [Real.exp_pos (2 * w)])
    linarith only [h]
  · apply add_le_add (le_refl 2)
    apply Real.log_le_log (by positivity)
    exact add_le_add (le_refl 1)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hwv (by norm_num)))

/-- Integrability of the actual logarithmic Poisson density. -/
theorem logReferencePoisson_integrable (w : ℝ) :
    Integrable (fun u : ℝ => logReferenceLogSymbol (w + u) / Real.cosh u) := by
  have hc : Integrable (fun u : ℝ => logReferenceLogSymbol w / Real.cosh u) := by
    simpa only [pow_zero, mul_one_div] using
      (RHTower.integrable_logSineSech_abs_pow 0).const_mul (logReferenceLogSymbol w)
  have hl : Integrable (fun u : ℝ => 2 * |u| / Real.cosh u) := by
    simpa only [pow_one, mul_div_assoc] using
      (RHTower.integrable_logSineSech_abs_pow 1).const_mul 2
  apply (hc.add hl).mono'
  · exact ((continuous_logReferenceLogSymbol.comp (continuous_const.add continuous_id)).div
      Real.continuous_cosh (fun u => (Real.cosh_pos u).ne')).aestronglyMeasurable
  · filter_upwards with u
    change ‖logReferenceLogSymbol (w + u) / Real.cosh u‖ ≤
      logReferenceLogSymbol w / Real.cosh u + 2 * |u| / Real.cosh u
    rw [Real.norm_of_nonneg (div_nonneg (logReferenceLogSymbol_nonneg _) (Real.cosh_pos u).le),
      ← add_div]
    apply div_le_div_of_nonneg_right _ (Real.cosh_pos u).le
    have h := logReferenceLogSymbol_shift_bound w u
    linarith only [h, le_abs_self (logReferenceLogSymbol (w + u) - logReferenceLogSymbol w)]

theorem one_le_logReferenceFactor (s : ℝ) : 1 ≤ logReferenceFactor s := by
  unfold logReferenceFactor
  apply Real.one_le_exp
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun u =>
    div_nonneg (logReferenceLogSymbol_nonneg _) (Real.cosh_pos u).le

theorem monotoneOn_logReferenceFactor : MonotoneOn logReferenceFactor (Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / (2 * Real.pi))
  apply integral_mono (logReferencePoisson_integrable _) (logReferencePoisson_integrable _)
  intro u
  apply div_le_div_of_nonneg_right _ (Real.cosh_pos u).le
  exact monotone_logReferenceLogSymbol
    (add_le_add (Real.log_le_log hs hst) (le_refl u))

/-- The positive factor has unit mass normalization at zero. -/
theorem tendsto_logReferenceFactor_at_zero :
    Tendsto logReferenceFactor (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
  have hi : Integrable (fun u : ℝ => logReferenceLogSymbol u / Real.cosh u) := by
    simpa only [zero_add] using logReferencePoisson_integrable 0
  have hlim : Tendsto (fun s : ℝ => ∫ u : ℝ,
      logReferenceLogSymbol (Real.log s + u) / Real.cosh u)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (∫ _ : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => logReferenceLogSymbol u / Real.cosh u)
    · exact Filter.Eventually.of_forall fun s =>
        ((continuous_logReferenceLogSymbol.comp (continuous_const.add continuous_id)).div
          Real.continuous_cosh (fun u => (Real.cosh_pos u).ne')).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with s hs hs1
      filter_upwards with u
      rw [Real.norm_of_nonneg (div_nonneg (logReferenceLogSymbol_nonneg _) (Real.cosh_pos u).le)]
      apply div_le_div_of_nonneg_right _ (Real.cosh_pos u).le
      apply monotone_logReferenceLogSymbol
      have hlog := Real.log_nonpos (le_of_lt hs) hs1.le
      linarith only [hlog]
    · exact hi
    · filter_upwards with u
      have hc : Continuous (fun s : ℝ => Real.log (positiveLogarithmicSymbol (s * Real.exp u))) :=
        (continuous_positiveLogarithmicSymbol.comp (continuous_id.mul continuous_const)).log
          (fun s => (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol _)).ne')
      have ht : Tendsto (fun s : ℝ => Real.log (positiveLogarithmicSymbol (s * Real.exp u)))
          (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
        simpa only [zero_mul, positiveLogarithmicSymbol, zero_pow (by norm_num : 2 ≠ 0),
          add_zero, Real.log_one, mul_zero] using
          (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
      have he : Tendsto (fun s : ℝ => logReferenceLogSymbol (Real.log s + u))
          (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
        apply ht.congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [logReferenceLogSymbol_eq_log, Real.exp_add, Real.exp_log hs]
      simpa only [zero_div] using he.div_const (Real.cosh u)
  simp only [integral_zero] at hlim
  change Tendsto (fun s : ℝ => Real.exp ((1 / (2 * Real.pi)) * ∫ u : ℝ,
    logReferenceLogSymbol (Real.log s + u) / Real.cosh u))
    (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1)
  simpa only [Function.comp_def, mul_zero, Real.exp_zero] using
    Real.continuous_exp.continuousAt.tendsto.comp (hlim.const_mul (1 / (2 * Real.pi)))

#print axioms tendsto_logReferenceFactor_at_zero

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
