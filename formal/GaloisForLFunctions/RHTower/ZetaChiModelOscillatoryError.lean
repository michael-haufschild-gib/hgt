import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import GaloisForLFunctions.RHTower.ZetaChiConductorOrientation
import GaloisForLFunctions.RHTower.ZetaChiIntegerGradeAmplitude

/-!
# Oscillatory error of the exact chi conductor model

The model error is factored as a slowly varying relative amplitude times the
actual integer chi grade. The source Hardy phase and phase-velocity remainders
then retain cancellation on every dyadic subinterval and under full complex
amplitude variation. No pointwise chi error is integrated absolutely.
-/

noncomputable section
open Complex MeasureTheory Set
namespace RHTower

private def chiModelRelativeError (k : ℤ) (t : ℝ) : ℂ :=
  1 - bourgainOscillation
    (2 * (k : ℝ) * (gammaHardyTheta t - gammaHardyThetaMain t - gammaHardyPhaseOffset))

private def chiModelRelativeErrorDeriv (k : ℤ) (t : ℝ) : ℂ :=
  -(bourgainOscillation
    (2 * (k : ℝ) * (gammaHardyTheta t - gammaHardyThetaMain t - gammaHardyPhaseOffset)) *
      (((2 * (k : ℝ) * (gammaHardyPhaseRate t -
        Real.log (t / (2 * Real.pi)) / 2) : ℝ) : ℂ) * I))

private theorem hasDerivAt_chiModelRelativeError (k : ℤ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (chiModelRelativeError k) (chiModelRelativeErrorDeriv k t) t := by
  have he := ((((hasDerivAt_gammaHardyTheta t).sub
    (hasDerivAt_gammaHardyThetaMain ht)).sub_const gammaHardyPhaseOffset).const_mul
      (2 * (k : ℝ)))
  have hd := (he.ofReal_comp.mul_const I).cexp.const_sub 1
  unfold chiModelRelativeError chiModelRelativeErrorDeriv bourgainOscillation
  simpa only [Pi.sub_apply, zero_sub, mul_comm I] using! hd

private theorem norm_chiModelRelativeError_le (k : ℤ) {t : ℝ} (ht : 4 ≤ t) :
    ‖chiModelRelativeError k t‖ ≤ 26 * |(k : ℝ)| / t := by
  have hphase := norm_bourgainOscillation_sub_le 0
    (2 * (k : ℝ) * (gammaHardyTheta t - gammaHardyThetaMain t - gammaHardyPhaseOffset))
  have hz : bourgainOscillation 0 = 1 := by simp [bourgainOscillation]
  rw [hz, zero_sub, abs_neg, abs_mul, abs_mul] at hphase
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hphase
  exact hphase.trans (by
    calc
      _ ≤ 2 * |(k : ℝ)| * (13 / t) :=
        mul_le_mul_of_nonneg_left (abs_gammaHardyTheta_sub_main_sub_offset_le ht)
          (by positivity)
      _ = _ := by ring)

private theorem norm_chiModelRelativeErrorDeriv_le (k : ℤ) {t : ℝ} (ht : 4 ≤ t) :
    ‖chiModelRelativeErrorDeriv k t‖ ≤ 26 * |(k : ℝ)| / t ^ 2 := by
  unfold chiModelRelativeErrorDeriv
  rw [norm_neg, norm_mul, norm_bourgainOscillation, one_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * |(k : ℝ)| * (13 / t ^ 2) :=
      mul_le_mul_of_nonneg_left (gammaHardyPhaseRate_sub_log_conductor_integrable_bound ht)
        (by positivity)
    _ = _ := by ring

/-- The chi/model difference is an actual slow amplitude times the exact chi grade.
The oscillation is retained instead of integrating its pointwise norm. -/
private theorem chiModelRelativeError_mul_actual (k : ℤ) (t : ℝ) :
    chiModelRelativeError k t * zetaChi (linePt t) ^ k =
      zetaChi (linePt t) ^ k - bourgainOscillation (Real.pi / 4) ^ k *
        Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I) := by
  rw [chiModelRelativeError, sub_mul, one_mul]
  congr 1
  rw [← bourgainOscillation_hardyPhaseOffset,
    zetaChi_line_eq_exp_neg_two_theta, ← Complex.exp_int_mul]
  unfold bourgainOscillation
  rw [← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold gammaHardyThetaMain
  push_cast
  ring

/-- Every nonzero exact chi grade transfers to its fixed conductor model with a
vanishing oscillatory integral error, uniformly in real Dirichlet frequency. -/
theorem norm_integral_zetaChi_integerGrade_sub_model_le
    {T a b : ℝ} (hT : 4 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T)
    {k : ℤ} (hk : k ≠ 0) (freq : ℝ) :
    ‖∫ t in a..b, (zetaChi (linePt t) ^ k - bourgainOscillation (Real.pi / 4) ^ k *
        Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)) *
      Complex.exp (((freq * t : ℝ) : ℂ) * I)‖ ≤
      (6 / Real.sqrt (|(k : ℝ)| / (100 * T))) * (52 * |(k : ℝ)| / T) := by
  have hT0 : 0 < T := by linarith
  have ht (x : ℝ) (hx : x ∈ uIcc a b) : 4 ≤ x ∧ T ≤ x ∧ x ≤ 2 * T := by
    rw [uIcc_of_le hab] at hx
    exact ⟨hT.trans (ha.trans hx.1), ha.trans hx.1, hx.2.trans hb⟩
  have hderivc : ContinuousOn (chiModelRelativeErrorDeriv k) (uIcc a b) := by
    have htheta : ContinuousOn gammaHardyTheta (uIcc a b) :=
      fun x _ => (hasDerivAt_gammaHardyTheta x).continuousAt.continuousWithinAt
    have hmain : ContinuousOn gammaHardyThetaMain (uIcc a b) :=
      fun x hx => (hasDerivAt_gammaHardyThetaMain (by linarith [(ht x hx).1])).continuousAt.continuousWithinAt
    have harg : ContinuousOn (fun x : ℝ => x / (2 * Real.pi)) (uIcc a b) :=
      continuousOn_id.div_const _
    have hlog := harg.log (fun x hx =>
      div_ne_zero (ne_of_gt (show 0 < x by linarith [(ht x hx).1])) (by positivity))
    have hp : ContinuousOn (fun x => 2 * (k : ℝ) *
        (gammaHardyTheta x - gammaHardyThetaMain x - gammaHardyPhaseOffset)) (uIcc a b) :=
      continuousOn_const.mul ((htheta.sub hmain).sub continuousOn_const)
    have hrate : ContinuousOn (fun x => 2 * (k : ℝ) *
        (gammaHardyPhaseRate x - Real.log (x / (2 * Real.pi)) / 2)) (uIcc a b) :=
      continuousOn_const.mul (continuous_gammaHardyPhaseRate.continuousOn.sub (hlog.div_const 2))
    exact ((Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hp))).mul
      ((Complex.continuous_ofReal.comp_continuousOn hrate).mul continuousOn_const)).neg
  have hbound := norm_integral_complexAmplitude_mul_zetaChi_line_zpow_mul_exp_le
    hT ha hab hb hk freq
    (fun x hx => hasDerivAt_chiModelRelativeError k (by linarith [(ht x hx).1]))
    hderivc.intervalIntegrable
  have heq : (∫ t in a..b, (zetaChi (linePt t) ^ k - bourgainOscillation (Real.pi / 4) ^ k *
        Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)) *
      Complex.exp (((freq * t : ℝ) : ℂ) * I)) =
      ∫ t in a..b, chiModelRelativeError k t *
        (zetaChi (linePt t) ^ k * Complex.exp (((freq * t : ℝ) : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← chiModelRelativeError_mul_actual, mul_assoc]
  rw [heq]
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hbT : T ≤ b := ha.trans hab
  have hbe := (norm_chiModelRelativeError_le k (hT.trans hbT)).trans
    (div_le_div_of_nonneg_left (by positivity) hT0 hbT)
  have hvar : (∫ x in a..b, ‖chiModelRelativeErrorDeriv k x‖) ≤
      26 * |(k : ℝ)| / T := by
    calc
      _ ≤ ∫ x in a..b, 26 * |(k : ℝ)| / T ^ 2 :=
        intervalIntegral.integral_mono_on hab hderivc.norm.intervalIntegrable
          (continuous_const.intervalIntegrable _ _) (fun x hx => by
            have hx' : x ∈ uIcc a b := by rwa [uIcc_of_le hab]
            apply (norm_chiModelRelativeErrorDeriv_le k (ht x hx').1).trans
            apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hT0)
            nlinarith [(ht x hx').2.1])
      _ = (b - a) * (26 * |(k : ℝ)| / T ^ 2) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ T * (26 * |(k : ℝ)| / T ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 26 * |(k : ℝ)| / T := by field_simp
  calc
    _ ≤ 26 * |(k : ℝ)| / T + 26 * |(k : ℝ)| / T := add_le_add hbe hvar
    _ = _ := by ring

private theorem continuous_chiModelRelativeError (k : ℤ) :
    Continuous (chiModelRelativeError k) := by
  have htheta : Continuous gammaHardyTheta :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_gammaHardyTheta t).continuousAt)
  have hmain : Continuous gammaHardyThetaMain := by
    have hm := ((Real.continuous_mul_log.comp (continuous_id.div_const (2 * Real.pi))).const_mul
      Real.pi).sub (continuous_id.div_const 2)
    apply hm.congr
    intro t
    unfold gammaHardyThetaMain
    dsimp only [Function.comp_apply, id_eq, Pi.sub_apply]
    field_simp [Real.pi_ne_zero]
  unfold chiModelRelativeError bourgainOscillation
  exact continuous_const.sub (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.mul
      ((htheta.sub hmain).sub continuous_const)))))

/-- Full smooth complex amplitudes preserve the actual chi/model cancellation,
with endpoint norm and complete derivative variation paid. -/
theorem norm_integral_complexAmplitude_mul_zetaChi_integerGrade_sub_model_le
    {T a b : ℝ} (hT : 4 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T)
    {k : ℤ} (hk : k ≠ 0) (freq : ℝ) {A A' : ℝ → ℂ}
    (hA : ∀ x ∈ uIcc a b, HasDerivAt A (A' x) x)
    (hA' : IntervalIntegrable A' volume a b) :
    ‖∫ t in a..b, A t *
      ((zetaChi (linePt t) ^ k - bourgainOscillation (Real.pi / 4) ^ k *
        Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)) *
        Complex.exp (((freq * t : ℝ) : ℂ) * I))‖ ≤
      ((6 / Real.sqrt (|(k : ℝ)| / (100 * T))) * (52 * |(k : ℝ)| / T)) *
        (‖A b‖ + ∫ x in a..b, ‖A' x‖) := by
  let f : ℝ → ℂ := fun t =>
    (zetaChi (linePt t) ^ k - bourgainOscillation (Real.pi / 4) ^ k *
      Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)) *
      Complex.exp (((freq * t : ℝ) : ℂ) * I)
  let F : ℝ → ℂ := fun x => ∫ t in a..x, f t
  have hf : Continuous f := by
    apply ((continuous_chiModelRelativeError k).mul
      (continuous_zetaChiCriticalGradeIntegrand k freq)).congr
    intro t
    dsimp [f]
    rw [← mul_assoc, chiModelRelativeError_mul_actual]
  apply norm_integral_complexAmplitude_mul_deriv_le hab hA
    (v := F) (v' := f)
  · intro x _
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a x)
      (hf.stronglyMeasurableAtFilter volume (nhds x)) hf.continuousAt
  · exact hA'
  · exact hf.intervalIntegrable a b
  · exact intervalIntegral.integral_same
  · intro x hx
    exact norm_integral_zetaChi_integerGrade_sub_model_le hT ha hx.1 (hx.2.trans hb) hk freq

end RHTower
