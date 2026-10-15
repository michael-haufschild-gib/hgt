import GaloisForLFunctions.RHTower.LogSineQuantileProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact sech coordinate for the logarithmic sine quantile clock

The fixed map `t(u)=2 arctan(exp u)/pi` identifies the original reciprocal-profile
clock with `P_delta(u)/pi`, where the speed of `P_delta` is
`1 / (1 + delta log(1 + cosh u))`. The clock is odd, strictly increasing and
contractive. For positive delta it obeys an explicit logarithmic upper bound;
as delta decreases to zero, it tends pointwise to the identity.

The coordinate identity retains the literal profile from the conductance theorem.
These are the source estimates needed for the entire-transform/nonreal-mode test;
no spectral or RH conclusion is asserted here.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

/-- Fixed coordinate identifying the sine quantile profile with the sech density. -/
def logSineBaseCoordinate (u : ℝ) : ℝ := 2 * Real.arctan (Real.exp u) / Real.pi

private theorem inv_cosh_exp (u : ℝ) :
    2 * Real.exp u / (1 + Real.exp u ^ 2) = 1 / Real.cosh u := by
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

theorem logSineBaseCoordinate_mem (u : ℝ) : logSineBaseCoordinate u ∈ Ioo (0 : ℝ) 1 := by
  have ha := Real.arctan_pos.mpr (Real.exp_pos u)
  have hb := Real.arctan_lt_pi_div_two (Real.exp u)
  constructor
  · exact div_pos (by positivity) Real.pi_pos
  · unfold logSineBaseCoordinate
    apply (div_lt_one Real.pi_pos).mpr
    linarith

theorem logSineBaseCoordinate_zero : logSineBaseCoordinate 0 = 1 / 2 := by
  unfold logSineBaseCoordinate
  rw [Real.exp_zero, Real.arctan_one]
  field_simp
  ring

theorem logSineBaseCoordinate_neg (u : ℝ) :
    logSineBaseCoordinate (-u) = 1 - logSineBaseCoordinate u := by
  unfold logSineBaseCoordinate
  rw [Real.exp_neg, Real.arctan_inv_of_pos (Real.exp_pos u)]
  field_simp

theorem hasDerivAt_logSineBaseCoordinate (u : ℝ) :
    HasDerivAt logSineBaseCoordinate (1 / (Real.pi * Real.cosh u)) u := by
  have hd := (((Real.hasDerivAt_exp u).arctan).const_mul 2).div_const Real.pi
  have he : 2 * (1 / (1 + Real.exp u ^ 2) * Real.exp u) / Real.pi =
      1 / (Real.pi * Real.cosh u) := by
    calc
      _ = (2 * Real.exp u / (1 + Real.exp u ^ 2)) / Real.pi := by ring
      _ = _ := by rw [inv_cosh_exp]; simp [div_eq_mul_inv, mul_comm]
  rw [he] at hd
  exact hd

theorem sin_logSineBaseCoordinate (u : ℝ) :
    Real.sin (Real.pi * logSineBaseCoordinate u) = 1 / Real.cosh u := by
  have he : Real.pi * logSineBaseCoordinate u = 2 * Real.arctan (Real.exp u) := by
    unfold logSineBaseCoordinate
    field_simp
  rw [he, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan, ← inv_cosh_exp]
  have hs := Real.sq_sqrt (show 0 ≤ 1 + Real.exp u ^ 2 by positivity)
  have hsn : Real.sqrt (1 + Real.exp u ^ 2) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The regularized speed denominator in the fixed sech coordinate. -/
def logSineClockDenom (δ u : ℝ) : ℝ := 1 + δ * Real.log (1 + Real.cosh u)

theorem logSineProfile_baseCoordinate (δ u : ℝ) :
    logSineProfile δ (logSineBaseCoordinate u) =
      logSineClockDenom δ u / Real.cosh u := by
  unfold logSineProfile
  rw [sin_logSineBaseCoordinate, logSineLift_eq (by positivity)]
  simp only [one_div_one_div]
  unfold logSineClockDenom
  ring

theorem logSineClockDenom_ge_one {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    1 ≤ logSineClockDenom δ u := by
  have hl : 0 ≤ Real.log (1 + Real.cosh u) :=
    Real.log_nonneg (by linarith [Real.cosh_pos u])
  unfold logSineClockDenom
  linarith [mul_nonneg hδ hl]

theorem continuous_logSineClockDenom (δ : ℝ) : Continuous (logSineClockDenom δ) := by
  unfold logSineClockDenom
  exact continuous_const.add (continuous_const.mul
    ((continuous_const.add Real.continuous_cosh).log (fun u : ℝ => (add_pos zero_lt_one (Real.cosh_pos u)).ne')))

def logSineClock (δ u : ℝ) : ℝ := ∫ v in (0 : ℝ)..u, 1 / logSineClockDenom δ v

theorem continuous_logSineClockSpeed {δ : ℝ} (hδ : 0 ≤ δ) :
    Continuous (fun u => 1 / logSineClockDenom δ u) := by
  exact continuous_const.div (continuous_logSineClockDenom δ)
    (fun u => ne_of_gt (lt_of_lt_of_le zero_lt_one (logSineClockDenom_ge_one hδ u)))

theorem hasDerivAt_logSineClock {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    HasDerivAt (logSineClock δ) (1 / logSineClockDenom δ u) u := by
  have hc := continuous_logSineClockSpeed hδ
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem continuous_logSineClock {δ : ℝ} (hδ : 0 ≤ δ) : Continuous (logSineClock δ) :=
  (show Differentiable ℝ (logSineClock δ) from
    fun u => (hasDerivAt_logSineClock hδ u).differentiableAt).continuous

theorem logSineClock_zero (δ : ℝ) : logSineClock δ 0 = 0 := by
  simp [logSineClock]

theorem logSineClock_zero_parameter (u : ℝ) : logSineClock 0 u = u := by
  simp [logSineClock, logSineClockDenom]

theorem logSineClock_neg (δ u : ℝ) : logSineClock δ (-u) = -logSineClock δ u := by
  have he : (fun v => 1 / logSineClockDenom δ (-v)) =
      fun v => 1 / logSineClockDenom δ v := by
    funext v
    simp [logSineClockDenom, Real.cosh_neg]
  unfold logSineClock
  have hi := intervalIntegral.integral_comp_neg (a := 0) (b := -u)
    (fun v => 1 / logSineClockDenom δ v)
  rw [he] at hi
  simpa only [neg_neg, neg_zero, intervalIntegral.integral_symm u 0] using hi

theorem logSineClockSpeed_pos {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    0 < 1 / logSineClockDenom δ u :=
  one_div_pos.mpr (lt_of_lt_of_le zero_lt_one (logSineClockDenom_ge_one hδ u))

theorem logSineClockSpeed_le_one {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    1 / logSineClockDenom δ u ≤ 1 := by
  exact (div_le_one (lt_of_lt_of_le zero_lt_one
    (logSineClockDenom_ge_one hδ u))).mpr (logSineClockDenom_ge_one hδ u)

theorem strictMono_logSineClock {δ : ℝ} (hδ : 0 ≤ δ) : StrictMono (logSineClock δ) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_logSineClock hδ) (logSineClockSpeed_pos hδ)

theorem logSineClock_nonneg {δ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) :
    0 ≤ logSineClock δ u := by
  simpa only [logSineClock_zero] using (strictMono_logSineClock hδ).monotone hu

theorem abs_logSineClock {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    |logSineClock δ u| = logSineClock δ |u| := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu, abs_of_nonneg (logSineClock_nonneg hδ hu)]
  · have hn : 0 ≤ -u := by linarith
    rw [abs_of_neg (lt_of_not_ge hu), logSineClock_neg]
    have hp := logSineClock_nonneg hδ hn
    rw [logSineClock_neg] at hp
    rw [abs_of_nonpos (by linarith)]

theorem abs_logSineClock_le {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    |logSineClock δ u| ≤ |u| := by
  rw [abs_logSineClock hδ]
  have h := intervalIntegral.integral_mono (μ := volume) (abs_nonneg u)
    ((continuous_logSineClockSpeed hδ).intervalIntegrable 0 |u|)
    (continuous_const.intervalIntegrable 0 |u|)
    (fun v => logSineClockSpeed_le_one hδ v)
  simpa [logSineClock] using h

/-- Literal reciprocal-profile clock in the original quantile variable. -/
def logSineQuantileClock (δ t : ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..t, 1 / logSineProfile δ v

/-- Exact coordinate change, retaining the original profile and its pinned centre. -/
theorem logSineQuantileClock_baseCoordinate {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    logSineQuantileClock δ (logSineBaseCoordinate u) = logSineClock δ u / Real.pi := by
  have hg : ContinuousOn (fun t => 1 / logSineProfile δ t)
      (logSineBaseCoordinate '' uIcc 0 u) := by
    rintro t ⟨v, hv, rfl⟩
    exact (continuousAt_const.div
      (hasDerivAt_logSineProfile (logSineBaseCoordinate_mem v)).continuousAt
      (logSineProfile_pos hδ (logSineBaseCoordinate_mem v)).ne').continuousWithinAt
  have hc : Continuous (fun v : ℝ => 1 / (Real.pi * Real.cosh v)) :=
    continuous_const.div (continuous_const.mul Real.continuous_cosh)
      (fun v => (mul_pos Real.pi_pos (Real.cosh_pos v)).ne')
  have he := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := u)
    (fun v _ => hasDerivAt_logSineBaseCoordinate v) hc.continuousOn hg
  rw [logSineBaseCoordinate_zero] at he
  unfold logSineQuantileClock
  rw [← he]
  calc
    _ = ∫ v in (0 : ℝ)..u, (1 / Real.pi) * (1 / logSineClockDenom δ v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      simp only [Function.comp_apply, logSineProfile_baseCoordinate]
      have hd : logSineClockDenom δ v ≠ 0 :=
        (lt_of_lt_of_le zero_lt_one (logSineClockDenom_ge_one hδ v)).ne'
      field_simp [hd, (Real.cosh_pos v).ne']
    _ = _ := by rw [intervalIntegral.integral_const_mul]; unfold logSineClock; ring

private theorem log_one_add_cosh_lower (u : ℝ) :
    |u| / 2 ≤ Real.log (1 + Real.cosh u) := by
  apply (Real.le_log_iff_exp_le (add_pos zero_lt_one (Real.cosh_pos u))).mpr
  have hc : Real.cosh u = Real.cosh |u| := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (lt_of_not_ge hu), Real.cosh_neg]
  rw [hc, Real.cosh_eq]
  have he : Real.exp (|u| / 2) ^ 2 = Real.exp |u| := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith [sq_nonneg (Real.exp (|u| / 2) - 1), Real.exp_pos (-|u|)]

private theorem log_one_add_cosh_upper (u : ℝ) :
    Real.log (1 + Real.cosh u) ≤ |u| + Real.log 2 := by
  have he1 := Real.exp_le_exp.mpr (abs_nonneg u)
  rw [Real.exp_zero] at he1
  have he2 := Real.exp_le_exp.mpr (le_abs_self u)
  have he3 := Real.exp_le_exp.mpr (neg_le_abs u)
  have hb : 1 + Real.cosh u ≤ 2 * Real.exp |u| := by rw [Real.cosh_eq]; linarith
  calc
    _ ≤ Real.log (2 * Real.exp |u|) := Real.log_le_log
      (add_pos zero_lt_one (Real.cosh_pos u)) hb
    _ = _ := by rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]; ring

private theorem integral_logSineClock_upper {δ u : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) :
    (∫ v in (0 : ℝ)..u, 1 / (1 + δ * v / 2)) =
      (2 / δ) * Real.log (1 + δ * u / 2) := by
  have hi : IntervalIntegrable (fun v : ℝ => 1 / (1 + δ * v / 2)) volume 0 u := by
    apply ContinuousOn.intervalIntegrable_of_Icc hu
    exact continuousOn_const.div
      (continuousOn_const.add ((continuousOn_const.mul continuousOn_id).div_const 2))
      (fun v hv => by have hv0 : 0 ≤ v := hv.1; positivity)
  have hd : ∀ v ∈ uIcc (0 : ℝ) u,
      HasDerivAt (fun v => (2 / δ) * Real.log (1 + δ * v / 2))
        (1 / (1 + δ * v / 2)) v := by
    intro v hv
    rw [uIcc_of_le hu] at hv
    have hne : 1 + δ * v / 2 ≠ 0 := by have hv0 : 0 ≤ v := hv.1; positivity
    convert (((((hasDerivAt_id v).const_mul δ).div_const 2).const_add 1).log hne).const_mul
      (2 / δ) using 1 <;> first | rfl | (simp only [id_eq]; field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp

theorem logSineClock_log_upper {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    |logSineClock δ u| ≤ (2 / δ) * Real.log (1 + δ * |u| / 2) := by
  rw [abs_logSineClock hδ.le]
  have hi : IntervalIntegrable (fun v : ℝ => 1 / (1 + δ * v / 2)) volume 0 |u| := by
    apply ContinuousOn.intervalIntegrable_of_Icc (abs_nonneg u)
    exact continuousOn_const.div
      (continuousOn_const.add ((continuousOn_const.mul continuousOn_id).div_const 2))
      (fun v hv => by have hv0 : 0 ≤ v := hv.1; positivity)
  calc
    _ ≤ ∫ v in (0 : ℝ)..|u|, 1 / (1 + δ * v / 2) := by
      apply intervalIntegral.integral_mono_on (abs_nonneg u)
        ((continuous_logSineClockSpeed hδ.le).intervalIntegrable _ _) hi
      intro v hv
      have hv0 : 0 ≤ v := hv.1
      have hl := log_one_add_cosh_lower v
      rw [abs_of_nonneg hv0] at hl
      apply one_div_le_one_div_of_le (by positivity)
      unfold logSineClockDenom
      nlinarith
    _ = _ := integral_logSineClock_upper hδ (abs_nonneg u)

/-- The regularized clock tends to the identity as its parameter decreases to zero. -/
theorem tendsto_logSineClock_parameter_zero (u : ℝ) :
    Tendsto (fun δ : ℝ => logSineClock δ u) (𝓝[≥] 0) (𝓝 u) := by
  have hside : ∀ᶠ δ : ℝ in 𝓝[≥] 0, 0 ≤ δ := self_mem_nhdsWithin
  have hm : ∀ᶠ δ : ℝ in 𝓝[≥] 0,
      AEStronglyMeasurable (fun v => 1 / logSineClockDenom δ v)
        (volume.restrict (uIoc 0 u)) := by
    filter_upwards [hside] with δ hδ
    exact (continuous_logSineClockSpeed hδ).aestronglyMeasurable
  have hb : ∀ᶠ δ : ℝ in 𝓝[≥] 0,
      ∀ᵐ v : ℝ ∂volume, v ∈ uIoc 0 u → ‖1 / logSineClockDenom δ v‖ ≤ (1 : ℝ) := by
    filter_upwards [hside] with δ hδ
    filter_upwards with v hv
    rw [Real.norm_of_nonneg (logSineClockSpeed_pos hδ v).le]
    exact logSineClockSpeed_le_one hδ v
  have hl : ∀ᵐ v : ℝ ∂volume, v ∈ uIoc 0 u →
      Tendsto (fun δ : ℝ => 1 / logSineClockDenom δ v) (𝓝[≥] 0) (𝓝 (1 : ℝ)) := by
    filter_upwards with v hv
    have hc : ContinuousAt (fun δ : ℝ => 1 / logSineClockDenom δ v) 0 := by
      unfold logSineClockDenom
      exact continuousAt_const.div (continuousAt_const.add
        (continuousAt_id.mul continuousAt_const)) (by simp)
    simpa only [logSineClockDenom, zero_mul, add_zero, div_one] using!
      hc.tendsto.mono_left inf_le_left
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := 0) (b := u) (fun _ : ℝ => (1 : ℝ)) hm hb
      (continuous_const.intervalIntegrable _ _) hl
  simpa only [logSineClock, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    using h

end
end RHTower
