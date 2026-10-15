import GaloisForLFunctions.RHTower.LogSineQuantileClock
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import GaloisForLFunctions.HTGeometry.SechComplexFourierTransform
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Entire order-one transform of the logarithmic sine clock

The exact clock has every exponential moment against the fixed sech measure.
A positive, explicit exponential envelope proves integrability and global growth.
The complex moment-generating-function theorem then proves that the literal
clock transform is entire. It is even, equals pi at zero, and obeys
`norm H(z) <= exp(K (1+norm z) log(2+norm z))` for a fixed nonnegative K.

These source theorems are ingredients of the positive-Hankel spectral test.
This file does not assume or assert real zeros, nonreal zeros, or RH.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

private theorem clock_log_tangent_bound {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) :
    p * Real.log (1 + x) - x ≤ p * Real.log (1 + 2 * p) - x / 2 := by
  have ha : 0 < 1 + 2 * p := by positivity
  have hb : 0 < 1 + x := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl hp
  have he : p * ((1 + x) / (1 + 2 * p) - 1) =
      (p * x - 2 * p ^ 2) / (1 + 2 * p) := by field_simp; ring
  have ht : (p * x - 2 * p ^ 2) / (1 + 2 * p) ≤ x / 2 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith [sq_nonneg p]
  rw [he] at hm
  linarith

private theorem clock_log_affine_bound {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    Real.log (1 + c * x) ≤ Real.log (max 1 c) + Real.log (1 + x) := by
  have hC : 0 < max (1 : ℝ) c := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : 1 + c * x ≤ max 1 c * (1 + x) := by
    have h1 := le_max_left (1 : ℝ) c
    have h2 := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) c) hx
    nlinarith
  calc
    _ ≤ Real.log (max 1 c * (1 + x)) := Real.log_le_log (by positivity) hb
    _ = _ := Real.log_mul hC.ne' (by positivity)

theorem logSineSech_exponential_bound (u : ℝ) :
    1 / Real.cosh u ≤ 2 * Real.exp (-|u|) := by
  have hc : Real.cosh u = Real.cosh |u| := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (lt_of_not_ge hu), Real.cosh_neg]
  have he : Real.exp |u| ≤ 2 * Real.cosh u := by
    rw [hc, Real.cosh_eq]
    linarith [Real.exp_pos (-|u|)]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-|u|)).le
  have hid : Real.exp |u| * Real.exp (-|u|) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hid] at hm
  apply (div_le_iff₀ (Real.cosh_pos u)).mpr
  nlinarith

/-- Every polynomial absolute moment of the fixed sech measure is integrable. -/
theorem integrable_logSineSech_abs_pow (n : ℕ) :
    Integrable (fun u : ℝ => |u| ^ n / Real.cosh u) := by
  have h := (HTGeometry.integrable_abs_pow_mul_exp_neg_abs n (r := 1) zero_lt_one).const_mul 2
  apply h.mono'
  · exact ((continuous_abs.pow n).div Real.continuous_cosh
      (fun u => (Real.cosh_pos u).ne')).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (abs_nonneg u) n) (Real.cosh_pos u).le)]
    have hb := mul_le_mul_of_nonneg_left (logSineSech_exponential_bound u)
      (pow_nonneg (abs_nonneg u) n)
    change |u| ^ n / Real.cosh u ≤ 2 * (|u| ^ n * Real.exp (-(1 : ℝ) * |u|))
    rw [neg_one_mul]
    calc
      _ = |u| ^ n * (1 / Real.cosh u) := by ring
      _ ≤ |u| ^ n * (2 * Real.exp (-|u|)) := hb
      _ = _ := by ring

/-- Explicit coefficient in a common integrable exponential envelope. -/
def logSineExponentialEnvelope (δ A : ℝ) : ℝ :=
  2 * Real.exp ((A * (2 / δ)) *
    (Real.log (max 1 (δ / 2)) + Real.log (1 + 2 * (A * (2 / δ)))))

/-- All exponential moments of the positive-parameter clock have an explicit bound
against one fixed decaying exponential. -/
theorem logSineClock_exponential_bound {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (u : ℝ) :
    Real.exp (A * |logSineClock δ u|) / Real.cosh u ≤
      logSineExponentialEnvelope δ A * Real.exp (-|u| / 2) := by
  set p := A * (2 / δ)
  have hp : 0 ≤ p := by positivity
  have hc := mul_le_mul_of_nonneg_left (logSineClock_log_upper hδ u) hA
  have hc' : A * |logSineClock δ u| ≤ p * Real.log (1 + (δ / 2) * |u|) := by
    rw [show 1 + (δ / 2) * |u| = 1 + δ * |u| / 2 by ring]
    dsimp [p]
    nlinarith [hc]
  have hl := mul_le_mul_of_nonneg_left
    (clock_log_affine_bound (show 0 ≤ δ / 2 by positivity) (abs_nonneg u)) hp
  have ht := clock_log_tangent_bound hp (abs_nonneg u)
  have htotal : A * |logSineClock δ u| - |u| ≤
      p * (Real.log (max 1 (δ / 2)) + Real.log (1 + 2 * p)) - |u| / 2 := by
    nlinarith
  calc
    _ = Real.exp (A * |logSineClock δ u|) * (1 / Real.cosh u) := by ring
    _ ≤ Real.exp (A * |logSineClock δ u|) * (2 * Real.exp (-|u|)) :=
      mul_le_mul_of_nonneg_left (logSineSech_exponential_bound u) (Real.exp_pos _).le
    _ = 2 * Real.exp (A * |logSineClock δ u| - |u|) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ 2 * Real.exp (p * (Real.log (max 1 (δ / 2)) +
        Real.log (1 + 2 * p)) - |u| / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htotal) (by positivity)
    _ = _ := by
      unfold logSineExponentialEnvelope
      rw [show -|u| / 2 = -(|u| / 2) by ring, Real.exp_sub, Real.exp_neg]
      dsimp [p]
      simp only [div_eq_mul_inv]
      ring

/-- Every exponential moment needed to differentiate the clock transform exists. -/
theorem integrable_logSineClock_exponential {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) :
    Integrable (fun u : ℝ => Real.exp (A * |logSineClock δ u|) / Real.cosh u) := by
  have hb : Integrable (fun u : ℝ => Real.exp (-|u| / 2)) := by
    convert HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (r := 1 / 2) (by positivity)
      using 1
    funext u
    simp only [pow_zero, one_mul]
    congr 1
    ring
  apply (hb.const_mul (logSineExponentialEnvelope δ A)).mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_logSineClock hδ.le).abs)).div
      Real.continuous_cosh (fun u => (Real.cosh_pos u).ne')).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_of_nonneg (div_pos (Real.exp_pos _) (Real.cosh_pos u)).le]
    exact logSineClock_exponential_bound hδ hA u

/-- Fixed sech measure used by the exact clock coordinate. Its mass is pi. -/
def logSineSechMeasure : Measure ℝ :=
  volume.withDensity (fun u => ENNReal.ofReal (1 / Real.cosh u))

private theorem measurable_logSineSechDensity :
    Measurable (fun u : ℝ => ENNReal.ofReal (1 / Real.cosh u)) :=
  (continuous_const.div Real.continuous_cosh
    (fun u => (Real.cosh_pos u).ne')).measurable.ennreal_ofReal

theorem integrable_logSineSechMeasure_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    Integrable g logSineSechMeasure ↔
      Integrable (fun u : ℝ => (1 / Real.cosh u) • g u) := by
  unfold logSineSechMeasure
  simpa only [ENNReal.toReal_ofReal (one_div_pos.mpr (Real.cosh_pos _)).le] using
    (integrable_withDensity_iff_integrable_smul' measurable_logSineSechDensity
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (g := g))

theorem integral_logSineSechMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    (∫ u, g u ∂logSineSechMeasure) = ∫ u : ℝ, (1 / Real.cosh u) • g u := by
  unfold logSineSechMeasure
  rw [integral_withDensity_eq_integral_toReal_smul measurable_logSineSechDensity
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with u
  rw [ENNReal.toReal_ofReal (one_div_pos.mpr (Real.cosh_pos u)).le]

/-- All real exponential tilts of the literal clock are integrable. -/
theorem logSineClock_integrableExpSet {δ : ℝ} (hδ : 0 < δ) :
    ProbabilityTheory.integrableExpSet (logSineClock δ) logSineSechMeasure = univ := by
  apply Set.eq_univ_of_forall
  intro a
  change Integrable (fun u => Real.exp (a * logSineClock δ u)) logSineSechMeasure
  rw [integrable_logSineSechMeasure_iff]
  simp only [smul_eq_mul]
  apply (integrable_logSineClock_exponential hδ (abs_nonneg a)).mono'
  · exact ((continuous_const.div Real.continuous_cosh
      (fun u => (Real.cosh_pos u).ne')).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_logSineClock hδ.le)))).aestronglyMeasurable
  · filter_upwards with u
    have he : (1 / Real.cosh u) * Real.exp (a * logSineClock δ u) =
        Real.exp (a * logSineClock δ u) / Real.cosh u := by ring
    rw [he, Real.norm_of_nonneg (div_pos (Real.exp_pos _) (Real.cosh_pos u)).le]
    apply div_le_div_of_nonneg_right _ (Real.cosh_pos u).le
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |a * logSineClock δ u| := le_abs_self _
      _ = _ := abs_mul _ _

/-- The unscaled Fourier transform in the exact sech coordinate. The original
quantile transform is this function at `z/pi`, divided by pi. -/
def logSineClockTransform (δ : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (Complex.I * z * (logSineClock δ u : ℂ)) / (Real.cosh u : ℂ)

theorem logSineClockTransform_eq_complexMGF (δ : ℝ) (z : ℂ) :
    logSineClockTransform δ z =
      ProbabilityTheory.complexMGF (logSineClock δ) logSineSechMeasure (Complex.I * z) := by
  unfold ProbabilityTheory.complexMGF logSineClockTransform
  rw [integral_logSineSechMeasure]
  apply integral_congr_ae
  filter_upwards with u
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- Positive regularization produces an entire transform from the literal source clock. -/
theorem analyticOnNhd_logSineClockTransform {δ : ℝ} (hδ : 0 < δ) :
    AnalyticOnNhd ℂ (logSineClockTransform δ) univ := by
  have he : logSineClockTransform δ = fun z =>
      ProbabilityTheory.complexMGF (logSineClock δ) logSineSechMeasure (Complex.I * z) :=
    funext (logSineClockTransform_eq_complexMGF δ)
  rw [he]
  intro z hz
  have ha : AnalyticAt ℂ (ProbabilityTheory.complexMGF (logSineClock δ) logSineSechMeasure)
      (Complex.I * z) := ProbabilityTheory.analyticAt_complexMGF (by
        rw [logSineClock_integrableExpSet hδ, interior_univ]
        exact mem_univ _)
  exact ha.comp (by fun_prop)

theorem logSineClockTransform_zero (δ : ℝ) : logSineClockTransform δ 0 = Real.pi := by
  have h := GaloisForLFunctions.HTGeometry.integral_cexp_div_cosh (z := 0) (by simp)
  simpa [logSineClockTransform] using h

theorem logSineClockTransform_even (δ : ℝ) (z : ℂ) :
    logSineClockTransform δ (-z) = logSineClockTransform δ z := by
  unfold logSineClockTransform
  calc
    _ = ∫ u : ℝ, Complex.exp (Complex.I * z * (logSineClock δ (-u) : ℂ)) /
        (Real.cosh (-u) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [logSineClock_neg, Real.cosh_neg, Complex.ofReal_neg]
      congr 2
      ring
    _ = _ := by
      simpa only [] using! (integral_neg_eq_self (fun u : ℝ =>
        Complex.exp (Complex.I * z * (logSineClock δ u : ℂ)) / (Real.cosh u : ℂ)) volume)

private theorem integrable_clock_tail : Integrable (fun u : ℝ => Real.exp (-|u| / 2)) := by
  have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (r := 1 / 2) (by positivity)
  apply h.congr
  filter_upwards with u
  simp only [pow_zero, one_mul]
  congr 1
  ring

private theorem integral_clock_tail : (∫ u : ℝ, Real.exp (-|u| / 2)) = 4 := by
  have h := HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 0 (r := 1 / 2) (by positivity)
  norm_num at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  ring

/-- Explicit global transform bound inherited from the clock's exponential envelope. -/
theorem norm_logSineClockTransform_le {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖logSineClockTransform δ z‖ ≤ 4 * logSineExponentialEnvelope δ ‖z‖ := by
  have hn (u : ℝ) :
      ‖Complex.exp (Complex.I * z * (logSineClock δ u : ℂ)) / (Real.cosh u : ℂ)‖ ≤
        Real.exp (‖z‖ * |logSineClock δ u|) / Real.cosh u := by
    rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos u)]
    apply div_le_div_of_nonneg_right _ (Real.cosh_pos u).le
    apply Real.exp_le_exp.mpr
    have he : (Complex.I * z * (logSineClock δ u : ℂ)).re =
        -(z.im * logSineClock δ u) := by simp [Complex.mul_re, Complex.mul_im]
    rw [he]
    calc
      _ ≤ |z.im * logSineClock δ u| := neg_le_abs _
      _ = |z.im| * |logSineClock δ u| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg _)
  calc
    _ ≤ ∫ u : ℝ,
        ‖Complex.exp (Complex.I * z * (logSineClock δ u : ℂ)) / (Real.cosh u : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, Real.exp (‖z‖ * |logSineClock δ u|) / Real.cosh u :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
        (integrable_logSineClock_exponential hδ (norm_nonneg z))
        (Filter.Eventually.of_forall hn)
    _ ≤ ∫ u : ℝ, logSineExponentialEnvelope δ ‖z‖ * Real.exp (-|u| / 2) :=
      integral_mono (integrable_logSineClock_exponential hδ (norm_nonneg z))
        (integrable_clock_tail.const_mul _) (logSineClock_exponential_bound hδ (norm_nonneg z))
    _ = _ := by rw [integral_const_mul, integral_clock_tail]; ring

private theorem clock_order_one_exponent {c L r : ℝ}
    (hc : 0 ≤ c) (hL : 0 ≤ L) (hr : 0 ≤ r) :
    Real.log 8 + c * r * (L + Real.log (1 + 2 * (c * r))) ≤
      (2 * Real.log 8 + 2 * c * (L + Real.log (max 1 (2 * c))) + c) *
        (1 + r) * Real.log (2 + r) := by
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by positivity : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hM : 0 ≤ L + Real.log (max 1 (2 * c)) :=
    add_nonneg hL (Real.log_nonneg (le_max_left _ _))
  have hl : 1 / 2 ≤ Real.log (2 + r) :=
    hl2.trans (Real.log_le_log (by positivity) (by linarith))
  have hlg := clock_log_affine_bound (show 0 ≤ 2 * c by positivity) hr
  have hlgr : Real.log (1 + r) ≤ Real.log (2 + r) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog : L + Real.log (1 + 2 * (c * r)) ≤
      L + Real.log (max 1 (2 * c)) + Real.log (2 + r) := by
    rw [show 2 * (c * r) = (2 * c) * r by ring]
    linarith
  have h1 : Real.log 8 ≤ 2 * Real.log 8 * ((1 + r) * Real.log (2 + r)) := by
    have hb : 1 / 2 ≤ (1 + r) * Real.log (2 + r) := by
      nlinarith [mul_nonneg hr (show 0 ≤ Real.log (2 + r) by linarith)]
    nlinarith
  have h2 : c * r * (L + Real.log (max 1 (2 * c))) ≤
      2 * c * (L + Real.log (max 1 (2 * c))) * ((1 + r) * Real.log (2 + r)) := by
    have hb : r ≤ 2 * ((1 + r) * Real.log (2 + r)) := by
      nlinarith [mul_nonneg hr (show 0 ≤ Real.log (2 + r) - 1 / 2 by linarith)]
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hc hM)
    nlinarith
  have h3 : c * r * Real.log (2 + r) ≤ c * ((1 + r) * Real.log (2 + r)) := by
    nlinarith [mul_nonneg hc (show 0 ≤ Real.log (2 + r) by linarith)]
  have h4 := mul_le_mul_of_nonneg_left hlog (mul_nonneg hc hr)
  nlinarith

/-- The explicit order-one growth envelope needed by the real-zero classification theorem. -/
theorem logSineClockTransform_order_one {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ,
      ‖logSineClockTransform δ z‖ ≤
        Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  let c := 2 / δ
  let L := Real.log (max 1 (δ / 2))
  have hc : 0 ≤ c := by positivity
  have hL : 0 ≤ L := Real.log_nonneg (le_max_left _ _)
  let K := 2 * Real.log 8 + 2 * c * (L + Real.log (max 1 (2 * c))) + c
  refine ⟨K, ?_, ?_⟩
  · have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hM : 0 ≤ Real.log (max 1 (2 * c)) := Real.log_nonneg (le_max_left _ _)
    dsimp [K]
    positivity
  · intro z
    calc
      _ ≤ 4 * logSineExponentialEnvelope δ ‖z‖ := norm_logSineClockTransform_le hδ z
      _ = Real.exp (Real.log 8 + c * ‖z‖ * (L + Real.log (1 + 2 * (c * ‖z‖)))) := by
        unfold logSineExponentialEnvelope
        rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < 8)]
        dsimp [c, L]
        simp only [mul_comm ‖z‖ (2 / δ)]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (clock_order_one_exponent hc hL (norm_nonneg z))

end
end RHTower
