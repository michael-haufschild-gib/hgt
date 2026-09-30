import GaloisForLFunctions.HTGeometry.PoissonKernelBound
import GaloisForLFunctions.RHTower.SteinhausModel

/-!
# The exact Poisson tilt of a Steinhaus Euler factor

The normalized squared Euler factor on a prime circle is the Poisson kernel.
This file constructs its probability law on the actual coordinate interval `[0,1]`
and proves that the negative log-modulus has mean `-log(1-r^2)`.
The centered increment is therefore exactly mean zero under this law.
These identities are source inputs to the BAG critical-mass barrier argument;
no barrier survival, low-moment decay, or recurrence estimate is assumed.
-/

noncomputable section

open MeasureTheory Complex Metric InnerProductSpace

namespace RHTower

/-- Normalized squared modulus of one Euler factor. -/
def steinhausEulerTiltWeight (r x : ℝ) : ℝ :=
  (1 - r ^ 2) / ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖ ^ 2

/-- Negative log-modulus of one Euler denominator. -/
def steinhausEulerTiltLog (r x : ℝ) : ℝ :=
  -Real.log ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖

/-- The log increment centered by its exact Poisson-tilted mean. -/
def steinhausEulerTiltCenteredLog (r x : ℝ) : ℝ :=
  steinhausEulerTiltLog r x + Real.log (1 - r ^ 2)

/-- The concrete change of measure on the Steinhaus coordinate interval. -/
def steinhausEulerTiltMeasure (r : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal (steinhausEulerTiltWeight r x))

private theorem norm_circlePhase (x : ℝ) :
    ‖circleMap (0 : ℂ) 1 (2 * Real.pi * x)‖ = 1 := by
  simp [circleMap, Complex.norm_exp]

private theorem one_sub_mul_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : (1 : ℂ) - (r : ℂ) * z ≠ 0 := by
  have hn : ‖(r : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact lt_of_le_of_lt (mul_le_of_le_one_right hr0 hz) hr1
  intro h
  have heq := sub_eq_zero.mp h
  rw [← heq, norm_one] at hn
  exact lt_irrefl _ hn

private theorem poissonKernel_eq_eulerWeight {r : ℝ} (hr0 : 0 ≤ r)
    {z : ℂ} (hz : ‖z‖ = 1) :
    poissonKernel 0 (r : ℂ) z = (1 - r ^ 2) / ‖(1 : ℂ) - (r : ℂ) * z‖ ^ 2 := by
  have hsq : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hden : ‖z - (r : ℂ)‖ ^ 2 = ‖(1 : ℂ) - (r : ℂ) * z‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_one, Complex.normSq_ofReal, hsq, map_mul, Complex.conj_ofReal,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  simp only [poissonKernel_def, sub_zero, hz, one_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr0, hden]

private theorem integral_circlePhase (f : ℂ → ℝ) :
    ∫ x, f (circleMap 0 1 (2 * Real.pi * x))
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = Real.circleAverage f 0 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_mul_left (fun t => f (circleMap 0 1 t))
    (by positivity : 2 * Real.pi ≠ 0)]
  simp [Real.circleAverage]

/-- The tilt density is strictly positive at every phase. -/
theorem steinhausEulerTiltWeight_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    0 < steinhausEulerTiltWeight r x := by
  apply div_pos
  · nlinarith
  · exact sq_pos_of_pos (norm_pos_iff.mpr
      (one_sub_mul_ne_zero hr0 hr1 (le_of_eq (norm_circlePhase x))))

/-- The density is continuous, with no singular phase for `r<1`. -/
theorem continuous_steinhausEulerTiltWeight {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (steinhausEulerTiltWeight r) := by
  unfold steinhausEulerTiltWeight
  refine continuous_const.div (by fun_prop) fun x => ?_
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (one_sub_mul_ne_zero hr0 hr1 (le_of_eq (norm_circlePhase x))))

/-- The real logarithmic increment is continuous. -/
theorem continuous_steinhausEulerTiltLog {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (steinhausEulerTiltLog r) := by
  unfold steinhausEulerTiltLog
  apply Continuous.neg
  refine Continuous.log (by fun_prop) fun x => ?_
  exact norm_ne_zero_iff.mpr
    (one_sub_mul_ne_zero hr0 hr1 (le_of_eq (norm_circlePhase x)))

/-- Poisson normalization: the tilted density has total mass one. -/
theorem integral_steinhausEulerTiltWeight {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ x, steinhausEulerTiltWeight r x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 1 := by
  have hw : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_iff_norm, abs_of_nonneg hr0] using hr1
  have hp := (harmonicOnNhd_const (E := ℂ) (1 : ℝ)).circleAverage_poissonKernel_smul hw
  have heq : ∀ x, steinhausEulerTiltWeight r x =
      poissonKernel 0 (r : ℂ) (circleMap 0 1 (2 * Real.pi * x)) := fun x =>
    (poissonKernel_eq_eulerWeight hr0 (norm_circlePhase x)).symm
  simp_rw [heq]
  rw [integral_circlePhase]
  change Real.circleAverage (fun z => poissonKernel 0 (r : ℂ) z * 1) 0 1 = 1 at hp
  simpa only [mul_one] using hp

/-- Exact weighted mean on the original uniform coordinate law. -/
theorem integral_steinhausEulerTiltWeight_mul_log {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ x, steinhausEulerTiltWeight r x * steinhausEulerTiltLog r x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = -Real.log (1 - r ^ 2) := by
  have hw : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_iff_norm, abs_of_nonneg hr0] using hr1
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => (1 : ℂ) - (r : ℂ) * z) (closedBall 0 1) := by
    intro z _
    exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have h0 : ∀ z ∈ closedBall (0 : ℂ) 1, (1 : ℂ) - (r : ℂ) * z ≠ 0 := by
    intro z hz
    apply one_sub_mul_ne_zero hr0 hr1
    simpa [mem_closedBall_iff_norm] using hz
  have hp := GaloisForLFunctions.HTGeometry.circleAverage_poissonKernel_log_norm hf h0 hw
  have hn : ‖(1 : ℂ) - (r : ℂ) * (r : ℂ)‖ = 1 - r ^ 2 := by
    have hh : (1 : ℂ) - (r : ℂ) * (r : ℂ) = ((1 - r ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith : 0 < 1 - r ^ 2)]
  have heq : ∀ x, steinhausEulerTiltWeight r x * steinhausEulerTiltLog r x =
      -(poissonKernel 0 (r : ℂ) (circleMap 0 1 (2 * Real.pi * x)) *
        Real.log ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖) := by
    intro x
    rw [poissonKernel_eq_eulerWeight hr0 (norm_circlePhase x)]
    simp [steinhausEulerTiltWeight, steinhausEulerTiltLog]
  simp_rw [heq]
  rw [integral_neg, integral_circlePhase
    (fun z => poissonKernel 0 (r : ℂ) z * Real.log ‖(1 : ℂ) - (r : ℂ) * z‖)]
  change -(Real.circleAverage (poissonKernel 0 (r : ℂ) •
    fun z => Real.log ‖(1 : ℂ) - (r : ℂ) * z‖) 0 1) = _
  rw [hp, hn]

/-- The concrete Euler tilt is a probability measure. -/
theorem isProbabilityMeasure_steinhausEulerTiltMeasure {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsProbabilityMeasure (steinhausEulerTiltMeasure r) := by
  constructor
  rw [steinhausEulerTiltMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((continuous_steinhausEulerTiltWeight hr0 hr1).integrableOn_Icc)
      (Filter.Eventually.of_forall fun x => (steinhausEulerTiltWeight_pos hr0 hr1 x).le),
    integral_steinhausEulerTiltWeight hr0 hr1]
  norm_num

/-- Exact change of measure for arbitrary real observables. -/
theorem integral_steinhausEulerTiltMeasure {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (f : ℝ → ℝ) :
    ∫ x, f x ∂steinhausEulerTiltMeasure r =
      ∫ x, steinhausEulerTiltWeight r x * f x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [steinhausEulerTiltMeasure, integral_withDensity_eq_integral_toReal_smul
    ((continuous_steinhausEulerTiltWeight hr0 hr1).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (steinhausEulerTiltWeight_pos hr0 hr1 x).le, smul_eq_mul]

/-- The logarithmic mean under the tilted coordinate law. -/
theorem integral_steinhausEulerTiltLog {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ x, steinhausEulerTiltLog r x ∂steinhausEulerTiltMeasure r = -Real.log (1 - r ^ 2) := by
  rw [integral_steinhausEulerTiltMeasure hr0 hr1,
    integral_steinhausEulerTiltWeight_mul_log hr0 hr1]

/-- The actual centered tilted logarithmic increment has mean zero. -/
theorem integral_steinhausEulerTiltCenteredLog {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ x, steinhausEulerTiltCenteredLog r x ∂steinhausEulerTiltMeasure r = 0 := by
  rw [integral_steinhausEulerTiltMeasure hr0 hr1]
  simp_rw [steinhausEulerTiltCenteredLog, mul_add]
  have hi₁ : Integrable (fun x => steinhausEulerTiltWeight r x * steinhausEulerTiltLog r x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ((continuous_steinhausEulerTiltWeight hr0 hr1).mul
      (continuous_steinhausEulerTiltLog hr0 hr1)).integrableOn_Icc
  have hi₂ : Integrable (fun x => steinhausEulerTiltWeight r x * Real.log (1 - r ^ 2))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ((continuous_steinhausEulerTiltWeight hr0 hr1).mul continuous_const).integrableOn_Icc
  rw [integral_add hi₁ hi₂,
    integral_steinhausEulerTiltWeight_mul_log hr0 hr1, integral_mul_const,
    integral_steinhausEulerTiltWeight hr0 hr1]
  ring

end RHTower
