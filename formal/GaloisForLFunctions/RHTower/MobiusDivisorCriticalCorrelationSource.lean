import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceSimpleJet
import GaloisForLFunctions.RHTower.DivisorContinuousHeadMellin
import GaloisForLFunctions.RHTower.DivisorUnsignedChannelExactMean
import GaloisForLFunctions.RHTower.DivisorSecondCenteredHyperbola
import GaloisForLFunctions.RHTower.ZetaRealStrip
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Source continuation for the literal critical autocorrelation

The actual Abel transform continues along the real interval `(-1, infinity)`.
Its left endpoint has a negative residue fixed by the positive unsigned
divisor mean. These are source inputs for the correlation tail argument;
no exponentially weighted correlation admission is asserted here.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace RHTower

/-- The existing exact unsigned mean, used without a numerical approximation. -/
def criticalCorrelationUnitMean : ℝ :=
  Real.log (2 * Real.pi) / 2 - Real.eulerMascheroniConstant - 1 / 4

theorem criticalCorrelationUnitMean_pos : 0 < criticalCorrelationUnitMean := by
  have hfloor := eventually_divisorUnsignedDilationChannel_one_ge_sqrt_coefficient
    (1 / 32) (by norm_num)
  have hbound : ∀ᶠ N : ℕ in atTop,
      (1 / 32 : ℝ) ≤ divisorUnsignedDilationChannel N 1 / Real.sqrt N := by
    filter_upwards [hfloor, eventually_ge_atTop (1 : ℕ)] with N hN hN1
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hN1))]
    norm_num at hN
    exact hN
  have h := le_of_tendsto_of_tendsto tendsto_const_nhds
    tendsto_divisorUnsignedDilationChannel_one_div_sqrt hbound
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 32) h

/-- The source value at zero is exactly its physical unsigned mean. -/
theorem divisorSourceEntire_zero_eq_unitMean :
    divisorSourceEntire 0 = (criticalCorrelationUnitMean : ℂ) := by
  rw [divisorSourceEntire_eq (by norm_num), deriv_riemannZeta_zero, riemannZeta_zero]
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  dsimp [criticalCorrelationUnitMean]
  push_cast
  ring

/-- The pole-filled continuation of the actual logarithmic Abel transform. -/
def criticalAbelLaplaceContinuation (s : ℂ) : ℂ :=
  s * divisorSourceEntire (1 + s) /
    ((1 + s) * (3 + 2 * s) * zetaPoleUnit (1 + s))

theorem criticalAbelLaplaceContinuation_eq_step {s : ℂ} (hs : 0 < s.re) :
    criticalAbelLaplaceContinuation s =
      criticalStepSourceMellin (1 + s) / (3 + 2 * s) := by
  rw [criticalStepSourceMellin_eq_poleUnit_quotient (by simp; linarith)]
  dsimp [criticalAbelLaplaceContinuation]
  rw [div_div]
  congr 1 <;> ring

private theorem poleUnit_real_shift_ne_zero {x : ℝ} (hx : -1 < x) :
    zetaPoleUnit (1 + (x : ℂ)) ≠ 0 := by
  by_cases hx0 : x = 0
  · simp [hx0, zetaPoleUnit_one]
  have hxC : (1 : ℂ) + (x : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hx0 this
  rw [zetaPoleUnit_of_ne hxC]
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr hx0
  · by_cases hp : 0 < x
    · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx0
      have h := riemannZeta_real_strip_ne_zero (σ := 1 + x) (by linarith) (by linarith)
      simpa using h

/-- Local analyticity includes zero and every real point before the left pole. -/
theorem analyticAt_criticalAbelLaplaceContinuation_real {x : ℝ} (hx : -1 < x) :
    AnalyticAt ℂ criticalAbelLaplaceContinuation (x : ℂ) := by
  have h1 : (1 : ℂ) + (x : ℂ) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have h3 : (3 : ℂ) + 2 * (x : ℂ) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hb : AnalyticAt ℂ (fun s => divisorSourceEntire (1 + s)) (x : ℂ) :=
    (differentiable_divisorSourceEntire.analyticAt _).comp
      (analyticAt_const.add analyticAt_id)
  have hp : AnalyticAt ℂ (fun s => zetaPoleUnit (1 + s)) (x : ℂ) :=
    (differentiable_zetaPoleUnit.analyticAt _).comp
      (analyticAt_const.add analyticAt_id)
  exact (analyticAt_id.mul hb).div
    (((analyticAt_const.add analyticAt_id).mul
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id))).mul hp)
    (mul_ne_zero (mul_ne_zero h1 h3) (poleUnit_real_shift_ne_zero hx))

private theorem unit_mellin_two_integrand {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-(5 / 2 : ℂ) - 1) * (divisorContinuousUnitHead x : ℂ) =
      ((x ^ (-(7 / 2 : ℝ)) * divisorContinuousUnitHead x : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.le]
  congr 2
  push_cast
  ring

private theorem unit_mellin_two_integrable :
    IntegrableOn (fun x : ℝ => x ^ (-(7 / 2 : ℝ)) * divisorContinuousUnitHead x)
      (Ioi 0) := by
  have h := mellinConvergent_mobiusDivisorContinuousHead ∅
    (s := (5 / 2 : ℂ)) (by norm_num)
  simp only [mobiusDivisorContinuousHead, Finset.prod_empty, Nat.divisors_one,
    Finset.sum_singleton, ArithmeticFunction.moebius_apply_one, Int.cast_one,
    Real.sqrt_one, one_mul, Nat.cast_one, div_one] at h
  apply h.re.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ((x : ℂ) ^ (-(5 / 2 : ℂ) - 1) * (divisorContinuousUnitHead x : ℂ)).re = _
  rw [unit_mellin_two_integrand hx]
  rfl

private theorem unit_mellin_two_pos :
    0 < ∫ x in Ioi (0 : ℝ), x ^ (-(7 / 2 : ℝ)) * divisorContinuousUnitHead x := by
  apply (integral_pos_iff_support_of_nonneg_ae _ unit_mellin_two_integrable).mpr
  · have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support
        (fun x => x ^ (-(7 / 2 : ℝ)) * divisorContinuousUnitHead x) := by
      intro x hx
      exact (mul_pos (Real.rpow_pos_of_pos (by linarith [hx.1]) _)
        (divisorContinuousUnitHead_pos_first hx)).ne'
    apply lt_of_lt_of_le _ (measure_mono hsub)
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo (1 : ℝ) 2 ⊆ Ioi 0 from fun x hx => by
        change 0 < x; linarith [hx.1]), Real.volume_Ioo]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (divisorContinuousUnitHead_nonneg x)

/-- Positivity comes from the actual nonnegative unit source and its first block. -/
theorem divisorSourceEntire_two_re_pos : 0 < (divisorSourceEntire 2).re := by
  have he := mellin_divisorContinuousUnitHead (s := (5 / 2 : ℂ)) (by norm_num)
  norm_num only at he
  have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(5 / 2 : ℂ) - 1) *
      (divisorContinuousUnitHead x : ℂ)) (Ioi 0) := by
    apply unit_mellin_two_integrable.ofReal.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (unit_mellin_two_integrand hx).symm
  have hr := congrArg Complex.re he
  simp only [mellin, smul_eq_mul] at hr
  have hiR := integral_re hi
  simp only [RCLike.re_to_complex] at hiR
  rw [← hiR] at hr
  have heq : (∫ x in Ioi (0 : ℝ),
      ((x : ℂ) ^ (-(5 / 2 : ℂ) - 1) * (divisorContinuousUnitHead x : ℂ)).re) =
      ∫ x in Ioi (0 : ℝ), x ^ (-(7 / 2 : ℝ)) * divisorContinuousUnitHead x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [unit_mellin_two_integrand hx]
    rfl
  rw [heq] at hr
  norm_num [Complex.div_re] at hr
  linarith [unit_mellin_two_pos]

theorem criticalAbelLaplaceContinuation_one_re_pos :
    0 < (criticalAbelLaplaceContinuation 1).re := by
  have hpi : (0 : ℝ) < Real.pi ^ (2 : ℕ) := sq_pos_of_pos Real.pi_pos
  have hB := divisorSourceEntire_two_re_pos
  simp only [criticalAbelLaplaceContinuation]
  norm_num [zetaPoleUnit_of_ne (by norm_num : (2 : ℂ) ≠ 1), riemannZeta_two,
    Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq,
    pow_two]
  positivity

/-- Exact negative real residue of the source transform at its left endpoint. -/
theorem criticalAbelLaplaceContinuation_left_residue :
    Tendsto (fun x : ℝ => ((x + 1 : ℝ) : ℂ) *
      criticalAbelLaplaceContinuation (x : ℂ))
      (𝓝[>] (-1 : ℝ)) (𝓝 (-2 * (criticalCorrelationUnitMean : ℂ))) := by
  have hp0 : zetaPoleUnit 0 = (1 / 2 : ℂ) := by
    rw [zetaPoleUnit_of_ne (by norm_num)]
    norm_num [riemannZeta_zero]
  let F : ℂ → ℂ := fun s => s * divisorSourceEntire (1 + s) /
    ((3 + 2 * s) * zetaPoleUnit (1 + s))
  have hc : ContinuousAt F (-1 : ℂ) := by
    apply ContinuousAt.div
    · exact continuousAt_id.mul
        (differentiable_divisorSourceEntire.continuous.continuousAt.comp
          (continuousAt_const.add continuousAt_id))
    · exact (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).mul
        (differentiable_zetaPoleUnit.continuous.continuousAt.comp
          (continuousAt_const.add continuousAt_id))
    · norm_num [hp0]
  have hxlim : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℂ)) := by
    simpa using ((Complex.continuous_ofReal.tendsto (-1 : ℝ)).mono_left
      (show 𝓝[>] (-1 : ℝ) ≤ 𝓝 (-1) from nhdsWithin_le_nhds))
  have hlim := hc.tendsto.comp hxlim
  have hval : F (-1) = -2 * (criticalCorrelationUnitMean : ℂ) := by
    dsimp [F]
    norm_num [hp0, divisorSourceEntire_zero_eq_unitMean]
    ring
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change -1 < x at hx
  have hx0 : (1 : ℂ) + (x : ℂ) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  dsimp [F, criticalAbelLaplaceContinuation]
  push_cast
  rw [show ((1 : ℂ) + (x : ℂ)) * (3 + 2 * (x : ℂ)) *
      zetaPoleUnit (1 + (x : ℂ)) =
      (1 + (x : ℂ)) * ((3 + 2 * (x : ℂ)) * zetaPoleUnit (1 + (x : ℂ))) by ring,
    ← mul_div_assoc]
  rw [show ((x : ℂ) + 1) * ((x : ℂ) * divisorSourceEntire (1 + (x : ℂ))) =
      (1 + (x : ℂ)) * ((x : ℂ) * divisorSourceEntire (1 + (x : ℂ))) by ring,
    mul_div_mul_left _ _ hx0]

end RHTower
