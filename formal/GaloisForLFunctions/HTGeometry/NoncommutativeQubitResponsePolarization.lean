import GaloisForLFunctions.HTGeometry.NoncommutativeQubitExponentialFormation
import GaloisForLFunctions.HTGeometry.ResponsePolarizationFisherTailJeffreysEscape
import GaloisForLFunctions.HTGeometry.HyperbolicBounds
import GaloisForLFunctions.HTGeometry.MonotoneSymbolTailEstimate
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# Noncommutative qubit response polarization

Exact BKM response of the transverse Pauli exponential family, cubic response and finite Fisher
completion, diagonal-observer quartic response, logarithmic observed work, and linear hidden deficit.
-/

open Filter MeasureTheory Set Topology
open scoped Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One-dimensional Bogoliubov--Kubo--Mori response of the qubit family. -/
def qubitResponse (b t : ℝ) : ℝ :=
  b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t) +
    t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2

/-- Probability of the `Z=+1` outcome under diagonal observation. -/
def qubitObservedProbability (b t : ℝ) : ℝ :=
  (1 + qubitMean b t) / 2

/-- Classical Fisher response of the observed Bernoulli family. -/
def qubitObservedResponse (b t : ℝ) : ℝ :=
  qubitResponse b t ^ 2 / (1 - qubitMean b t ^ 2)

/-- Reflected complete quantum work. -/
def qubitReflectedQuantumWork (b t : ℝ) : ℝ :=
  qubitQuantumJeffreys b t (-t)

/-- Reflected Jeffreys work of the diagonal Bernoulli observer. -/
def qubitObservedWork (b t : ℝ) : ℝ :=
  2 * qubitMean b t *
    Real.log ((1 + qubitMean b t) / (1 - qubitMean b t))

/-- Complete quantum work missing from diagonal observation. -/
def qubitMeasurementDeficit (b t : ℝ) : ℝ :=
  qubitReflectedQuantumWork b t - qubitObservedWork b t

theorem qubitRadius_hasDerivAt {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u : ℝ => qubitRadius b u) (t / qubitRadius b t) t := by
  have hpoly : HasDerivAt (fun u : ℝ => u ^ 2 + b ^ 2) (2 * t) t := by
    simpa [id_eq] using
      ((hasDerivAt_id t).pow 2).add_const (b ^ 2)
  have harg : t ^ 2 + b ^ 2 ≠ 0 := by positivity
  have h := (Real.hasDerivAt_sqrt harg).comp t hpoly
  have hcoef : 1 / (2 * Real.sqrt (t ^ 2 + b ^ 2)) * (2 * t) =
      t / qubitRadius b t := by
    rw [qubitRadius]
    have hsqrt : Real.sqrt (t ^ 2 + b ^ 2) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by positivity)
    field_simp
  simpa [qubitRadius, Function.comp_def] using h.congr_deriv hcoef

theorem qubitFreeEnergy_hasDerivAt {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u : ℝ => qubitFreeEnergy b u) (qubitMean b t) t := by
  have hr := qubitRadius_hasDerivAt hb t
  have hcosh := hr.cosh.const_mul 2
  have hlog := hcosh.log
    (show 2 * Real.cosh (qubitRadius b t) ≠ 0 by positivity)
  have hcoef : (2 * (Real.sinh (qubitRadius b t) *
      (t / qubitRadius b t))) / (2 * Real.cosh (qubitRadius b t)) =
      qubitMean b t := by
    rw [qubitMean, Real.tanh_eq_sinh_div_cosh]
    field_simp [(qubitRadius_pos hb t).ne', (Real.cosh_pos _).ne']
  simpa [qubitFreeEnergy, Function.comp_def] using hlog.congr_deriv hcoef

theorem qubitMean_hasDerivAt {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u : ℝ => qubitMean b u) (qubitResponse b t) t := by
  have hr := qubitRadius_hasDerivAt hb t
  have hr0 : qubitRadius b t ≠ 0 := (qubitRadius_pos hb t).ne'
  have hratio := (hasDerivAt_id t).div hr hr0
  have htanh := (HTGeometry.hasDerivAt_tanh (qubitRadius b t)).comp t hr
  have h := hratio.mul htanh
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  have hb2 : b ^ 2 = qubitRadius b t ^ 2 - t ^ 2 := by
    nlinarith [hr2]
  have hcoef :
      ((1 * qubitRadius b t - t * (t / qubitRadius b t)) /
          qubitRadius b t ^ 2) * Real.tanh (qubitRadius b t) +
        (t / qubitRadius b t) *
          (1 / Real.cosh (qubitRadius b t) ^ 2 *
            (t / qubitRadius b t)) = qubitResponse b t := by
    rw [qubitResponse, hb2]
    field_simp [hr0, (Real.cosh_pos _).ne']
  refine (h.congr_deriv hcoef).congr_of_eventuallyEq ?_
  filter_upwards with u
  simp only [qubitMean, Function.comp_apply, id_eq, Pi.div_apply, Pi.mul_apply]

theorem qubitResponse_pos {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < qubitResponse b t := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htanh : 0 < Real.tanh (qubitRadius b t) := by
    have h := HTGeometry.tanh_strictMono hr
    simpa only [Real.tanh_zero] using h
  rw [qubitResponse]
  positivity

theorem continuous_qubitResponse {b : ℝ} (hb : 0 < b) :
    Continuous (qubitResponse b) := by
  have hrC : Continuous (fun t : ℝ => qubitRadius b t) := by
    change Continuous (fun t : ℝ => Real.sqrt (t ^ 2 + b ^ 2))
    fun_prop
  have htanhC : Continuous Real.tanh := by
    rw [show Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x by
      funext x
      exact Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')
  have hcoshC : Continuous (fun t : ℝ => Real.cosh (qubitRadius b t)) :=
    Real.continuous_cosh.comp hrC
  change Continuous (fun t : ℝ =>
    b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t) +
      t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2)
  exact (((continuous_const.pow 2).div (hrC.pow 3)
      (fun t => pow_ne_zero 3 (qubitRadius_pos hb t).ne')).mul
        (htanhC.comp hrC)).add
    (((continuous_id.pow 2).div (hrC.pow 2)
      (fun t => pow_ne_zero 2 (qubitRadius_pos hb t).ne')).div
        (hcoshC.pow 2) (fun t => pow_ne_zero 2 (Real.cosh_pos _).ne'))

theorem integral_qubitResponse {b : ℝ} (hb : 0 < b) (a c : ℝ) :
    (∫ t : ℝ in a..c, qubitResponse b t) =
      qubitMean b c - qubitMean b a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => qubitMean_hasDerivAt hb t)
    ((continuous_qubitResponse hb).intervalIntegrable a c)

theorem qubitQuantumJeffreys_eq_integral {b : ℝ} (hb : 0 < b) (s t : ℝ) :
    qubitQuantumJeffreys b s t =
      |s - t| * ∫ u : ℝ in min s t..max s t, qubitResponse b u := by
  rw [qubitQuantumJeffreys_eq hb, integral_qubitResponse hb]
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst, max_eq_right hst, abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  · rw [min_eq_right hts, max_eq_left hts, abs_of_nonneg (sub_nonneg.mpr hts)]

@[simp] theorem qubitRadius_neg (b t : ℝ) :
    qubitRadius b (-t) = qubitRadius b t := by
  simp [qubitRadius]

@[simp] theorem qubitMean_neg (b t : ℝ) :
    qubitMean b (-t) = -qubitMean b t := by
  rw [qubitMean, qubitMean, qubitRadius_neg]
  ring

@[simp] theorem qubitResponse_neg (b t : ℝ) :
    qubitResponse b (-t) = qubitResponse b t := by
  simp [qubitResponse]

theorem abs_lt_qubitRadius {b : ℝ} (hb : 0 < b) (t : ℝ) :
    |t| < qubitRadius b t := by
  rw [qubitRadius, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg t) (by nlinarith [sq_pos_of_pos hb])

theorem tendsto_qubitRadius_atTop {b : ℝ} (hb : 0 < b) :
    Tendsto (qubitRadius b) atTop atTop := by
  rw [tendsto_atTop]
  intro A
  filter_upwards [eventually_ge_atTop (max A 0)] with t ht
  have htA : A ≤ t := (le_max_left A 0).trans ht
  have ht0 : 0 ≤ t := (le_max_right A 0).trans ht
  exact htA.trans ((le_abs_self t).trans (abs_lt_qubitRadius hb t).le)

theorem tendsto_qubitRadius_div_self {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => qubitRadius b t / t) atTop (𝓝 1) := by
  have hbt : Tendsto (fun t : ℝ => b / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hroot : Tendsto (fun t : ℝ => Real.sqrt (1 + (b / t) ^ 2))
      atTop (𝓝 1) := by
    simpa using (hone.add (hbt.pow 2)).sqrt
  refine hroot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hlhs0 : 0 ≤ qubitRadius b t / t := div_nonneg (qubitRadius_pos hb t).le ht.le
  have hrhs0 : 0 ≤ Real.sqrt (1 + (b / t) ^ 2) := Real.sqrt_nonneg _
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  have hlhs2 : (qubitRadius b t / t) ^ 2 = 1 + (b / t) ^ 2 := by
    field_simp
    nlinarith [hr2]
  have hrhs2 : Real.sqrt (1 + (b / t) ^ 2) ^ 2 = 1 + (b / t) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith

theorem tendsto_self_div_qubitRadius {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t / qubitRadius b t) atTop (𝓝 1) := by
  have h := (tendsto_qubitRadius_div_self hb).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div, inv_one] using h

private theorem tanh_eq_expNegTwoRatio (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
  have hexp : Real.exp (-(2 * x)) = Real.exp (-x) / Real.exp x := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [Real.tanh_eq, hexp]
  field_simp [Real.exp_ne_zero x, Real.exp_ne_zero (-x)]

theorem tendsto_tanh_atTop_one : Tendsto Real.tanh atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_atTop_nhds_zero (by norm_num)
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have h := (hone.sub he).div (hone.add he)
    (by norm_num : (1 + (0 : ℝ)) ≠ 0)
  have h' : Tendsto
      ((fun x : ℝ => 1 - Real.exp (-(2 * x))) /
        (fun x : ℝ => 1 + Real.exp (-(2 * x)))) atTop (𝓝 1) := by
    simpa only [sub_zero, add_zero, div_one] using h
  rw [show Real.tanh = fun x : ℝ =>
    (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) by
      funext x
      exact tanh_eq_expNegTwoRatio x]
  refine h'.congr' ?_
  filter_upwards with x
  rfl

theorem tendsto_tanh_qubitRadius_atTop {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.tanh (qubitRadius b t)) atTop (𝓝 1) :=
  tendsto_tanh_atTop_one.comp (tendsto_qubitRadius_atTop hb)

theorem tendsto_qubitMean_atTop_one {b : ℝ} (hb : 0 < b) :
    Tendsto (qubitMean b) atTop (𝓝 1) := by
  change Tendsto (fun t : ℝ => t / qubitRadius b t *
    Real.tanh (qubitRadius b t)) atTop (𝓝 1)
  simpa only [mul_one] using
    (tendsto_self_div_qubitRadius hb).mul (tendsto_tanh_qubitRadius_atTop hb)

theorem inv_cosh_sq_le_four_exp_neg_two {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.cosh x ^ 2 ≤ 4 * Real.exp (-(2 * x)) := by
  have h := HTGeometry.cosh_rpow_neg_le (s := (2 : ℝ)) (by norm_num) x
  rw [show (-(2 : ℝ)) = -(2 : ℝ) by rfl,
    Real.rpow_neg (Real.cosh_pos x).le,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, abs_of_nonneg hx] at h
  norm_num at h ⊢
  simpa only [one_div] using h

private theorem tendsto_qubitResponse_cubic_first {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 3 *
      (b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t)))
      atTop (𝓝 (b ^ 2)) := by
  have hlim : Tendsto (fun t : ℝ =>
      b ^ 2 * (t / qubitRadius b t) ^ 3 * Real.tanh (qubitRadius b t))
      atTop (𝓝 (b ^ 2)) := by
    simpa only [one_pow, mul_one] using
      ((tendsto_const_nhds.mul ((tendsto_self_div_qubitRadius hb).pow 3)).mul
        (tendsto_tanh_qubitRadius_atTop hb))
  refine hlim.congr' ?_
  filter_upwards with t
  field_simp [(qubitRadius_pos hb t).ne']

private theorem qubitResponse_cubic_second_bounds {b : ℝ} (hb : 0 < b)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
      Real.cosh (qubitRadius b t) ^ 2) ∧
    t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
      Real.cosh (qubitRadius b t) ^ 2) ≤
      4 * t ^ 3 * Real.exp (-(2 * t)) := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htr : t ≤ qubitRadius b t :=
    (le_abs_self t).trans (abs_lt_qubitRadius hb t).le
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  have hfrac : t ^ 2 / qubitRadius b t ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hr)]
    nlinarith [sq_nonneg b]
  have hsech := inv_cosh_sq_le_four_exp_neg_two hr.le
  have hexp : Real.exp (-(2 * qubitRadius b t)) ≤ Real.exp (-(2 * t)) :=
    Real.exp_le_exp.mpr (by linarith)
  constructor
  · positivity
  · have hinner : t ^ 2 / qubitRadius b t ^ 2 /
        Real.cosh (qubitRadius b t) ^ 2 ≤
        4 * Real.exp (-(2 * qubitRadius b t)) := by
      calc
        t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2
            ≤ 1 / Real.cosh (qubitRadius b t) ^ 2 := by
              gcongr
        _ ≤ 4 * Real.exp (-(2 * qubitRadius b t)) := hsech
    calc
      t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
          Real.cosh (qubitRadius b t) ^ 2)
          ≤ t ^ 3 * (4 * Real.exp (-(2 * qubitRadius b t))) := by
            gcongr
      _ ≤ t ^ 3 * (4 * Real.exp (-(2 * t))) := by
            gcongr
      _ = 4 * t ^ 3 * Real.exp (-(2 * t)) := by ring

private theorem tendsto_qubitResponse_cubic_second {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
      Real.cosh (qubitRadius b t) ^ 2)) atTop (𝓝 0) := by
  have hdom : Tendsto (fun t : ℝ => 4 * t ^ 3 * Real.exp (-(2 * t)))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_mul_exp_neg_mul_atTop (b := (2 : ℝ)) (by norm_num) 3).const_mul 4
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with t
    ring
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (qubitResponse_cubic_second_bounds hb ht).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (qubitResponse_cubic_second_bounds hb ht).2

theorem tendsto_cubic_mul_qubitResponse {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 3 * qubitResponse b t) atTop (𝓝 (b ^ 2)) := by
  rw [show (fun t : ℝ => t ^ 3 * qubitResponse b t) =
      fun t : ℝ =>
        t ^ 3 * (b ^ 2 / qubitRadius b t ^ 3 *
          Real.tanh (qubitRadius b t)) +
        t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
          Real.cosh (qubitRadius b t) ^ 2) by
    funext t
    rw [qubitResponse]
    ring]
  simpa only [add_zero] using
    (tendsto_qubitResponse_cubic_first hb).add
      (tendsto_qubitResponse_cubic_second hb)

theorem qubitReflectedQuantumWork_eq {b : ℝ} (hb : 0 < b) (t : ℝ) :
    qubitReflectedQuantumWork b t =
      4 * t ^ 2 / qubitRadius b t * Real.tanh (qubitRadius b t) := by
  rw [qubitReflectedQuantumWork, qubitQuantumJeffreys_eq hb, qubitMean_neg,
    qubitMean]
  ring

theorem tendsto_qubitReflectedQuantumWork_div_four_mul {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => qubitReflectedQuantumWork b t / (4 * t))
      atTop (𝓝 1) := by
  refine (tendsto_qubitMean_atTop_one hb).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [qubitReflectedQuantumWork_eq hb, qubitMean]
  field_simp [ht.ne', (qubitRadius_pos hb t).ne']

theorem one_sub_self_div_qubitRadius {b : ℝ} (hb : 0 < b) (t : ℝ) :
    1 - t / qubitRadius b t =
      b ^ 2 / (qubitRadius b t * (qubitRadius b t + t)) := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have hsum : 0 < qubitRadius b t + t := by
    linarith [abs_lt_qubitRadius hb t, neg_le_abs t]
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  field_simp [hr.ne', hsum.ne']
  nlinarith

private theorem tendsto_sq_mul_one_sub_self_div_qubitRadius {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * (1 - t / qubitRadius b t))
      atTop (𝓝 (b ^ 2 / 2)) := by
  have hr := tendsto_qubitRadius_div_self hb
  have hden : Tendsto (fun t : ℝ =>
      (qubitRadius b t / t) * (qubitRadius b t / t + 1))
      atTop (𝓝 2) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hraw := hr.mul (hr.add hone)
    norm_num at hraw
    exact hraw
  have hquot : Tendsto (fun t : ℝ => b ^ 2 /
      ((qubitRadius b t / t) * (qubitRadius b t / t + 1)))
      atTop (𝓝 (b ^ 2 / 2)) :=
    tendsto_const_nhds.div hden (by norm_num)
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [one_sub_self_div_qubitRadius hb]
  field_simp [ht.ne', (qubitRadius_pos hb t).ne']

theorem one_sub_tanh_le_two_exp_neg_two {x : ℝ} :
    1 - Real.tanh x ≤ 2 * Real.exp (-(2 * x)) := by
  rw [tanh_eq_expNegTwoRatio]
  have he : 0 < Real.exp (-(2 * x)) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (-(2 * x)) := by positivity
  rw [show 1 - (1 - Real.exp (-(2 * x))) /
      (1 + Real.exp (-(2 * x))) =
      2 * Real.exp (-(2 * x)) / (1 + Real.exp (-(2 * x))) by
    field_simp
    ring]
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg (Real.exp (-(2 * x)))]

private theorem qubitMean_defect_second_bounds {b : ℝ} (hb : 0 < b)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ 2 * (t / qubitRadius b t) *
        (1 - Real.tanh (qubitRadius b t)) ∧
    t ^ 2 * (t / qubitRadius b t) *
        (1 - Real.tanh (qubitRadius b t)) ≤
      2 * t ^ 2 * Real.exp (-(2 * t)) := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htr : t ≤ qubitRadius b t :=
    (le_abs_self t).trans (abs_lt_qubitRadius hb t).le
  have hratio0 : 0 ≤ t / qubitRadius b t := div_nonneg ht hr.le
  have hratio1 : t / qubitRadius b t ≤ 1 := (div_le_one hr).mpr htr
  have hdefect0 : 0 ≤ 1 - Real.tanh (qubitRadius b t) :=
    sub_nonneg.mpr (Real.tanh_lt_one _).le
  have hdefect := one_sub_tanh_le_two_exp_neg_two (x := qubitRadius b t)
  have hexp : Real.exp (-(2 * qubitRadius b t)) ≤ Real.exp (-(2 * t)) :=
    Real.exp_le_exp.mpr (by linarith)
  constructor
  · positivity
  · calc
      t ^ 2 * (t / qubitRadius b t) *
          (1 - Real.tanh (qubitRadius b t))
          ≤ t ^ 2 * 1 * (2 * Real.exp (-(2 * qubitRadius b t))) := by
            gcongr
      _ ≤ t ^ 2 * 1 * (2 * Real.exp (-(2 * t))) := by
            gcongr
      _ = 2 * t ^ 2 * Real.exp (-(2 * t)) := by ring

private theorem tendsto_qubitMean_defect_second {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * (t / qubitRadius b t) *
      (1 - Real.tanh (qubitRadius b t))) atTop (𝓝 0) := by
  have hdom : Tendsto (fun t : ℝ => 2 * t ^ 2 * Real.exp (-(2 * t)))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_mul_exp_neg_mul_atTop (b := (2 : ℝ)) (by norm_num) 2).const_mul 2
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with t
    ring
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (qubitMean_defect_second_bounds hb ht).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (qubitMean_defect_second_bounds hb ht).2

theorem tendsto_sq_mul_one_sub_qubitMean {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * (1 - qubitMean b t))
      atTop (𝓝 (b ^ 2 / 2)) := by
  rw [show (fun t : ℝ => t ^ 2 * (1 - qubitMean b t)) =
      fun t : ℝ =>
        t ^ 2 * (1 - t / qubitRadius b t) +
        t ^ 2 * (t / qubitRadius b t) *
          (1 - Real.tanh (qubitRadius b t)) by
    funext t
    rw [qubitMean]
    ring]
  simpa only [add_zero] using
    (tendsto_sq_mul_one_sub_self_div_qubitRadius hb).add
      (tendsto_qubitMean_defect_second hb)

theorem tendsto_sq_mul_one_sub_qubitMean_sq {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * (1 - qubitMean b t ^ 2))
      atTop (𝓝 (b ^ 2)) := by
  have hsum : Tendsto (fun t : ℝ => 1 + qubitMean b t) atTop (𝓝 2) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := hone.add (tendsto_qubitMean_atTop_one hb)
    norm_num at h
    exact h
  have hprod := (tendsto_sq_mul_one_sub_qubitMean hb).mul hsum
  have hprod' : Tendsto (fun t : ℝ =>
      (t ^ 2 * (1 - qubitMean b t)) * (1 + qubitMean b t))
      atTop (𝓝 (b ^ 2)) := by
    norm_num at hprod
    exact hprod
  refine hprod'.congr' ?_
  filter_upwards with t
  ring

theorem abs_qubitMean_lt_one {b : ℝ} (hb : 0 < b) (t : ℝ) :
    |qubitMean b t| < 1 := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have hratio : |t| / qubitRadius b t < 1 :=
    (div_lt_one hr).mpr (abs_lt_qubitRadius hb t)
  have hratio0 : 0 ≤ |t| / qubitRadius b t := div_nonneg (abs_nonneg t) hr.le
  have htanh : |Real.tanh (qubitRadius b t)| < 1 :=
    (abs_lt).mpr ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  rw [qubitMean, abs_mul, abs_div, abs_of_pos hr]
  calc
    |t| / qubitRadius b t * |Real.tanh (qubitRadius b t)|
        ≤ |t| / qubitRadius b t * 1 :=
          mul_le_mul_of_nonneg_left htanh.le hratio0
    _ < 1 := by simpa only [mul_one] using hratio

theorem qubitObservedProbability_hasDerivAt {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u : ℝ => qubitObservedProbability b u)
      (qubitResponse b t / 2) t := by
  have h := ((hasDerivAt_const t 1).add (qubitMean_hasDerivAt hb t)).div_const 2
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with u
  simp only [qubitObservedProbability, Pi.add_apply]

@[simp] theorem qubitObservedProbability_neg (b t : ℝ) :
    qubitObservedProbability b (-t) = 1 - qubitObservedProbability b t := by
  rw [qubitObservedProbability, qubitObservedProbability, qubitMean_neg]
  ring

theorem qubitObservedProbability_pos {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < qubitObservedProbability b t := by
  rw [qubitObservedProbability]
  have h := (abs_lt.mp (abs_qubitMean_lt_one hb t)).1
  linarith

theorem qubitObservedProbability_lt_one {b : ℝ} (hb : 0 < b) (t : ℝ) :
    qubitObservedProbability b t < 1 := by
  rw [qubitObservedProbability]
  have h := (abs_lt.mp (abs_qubitMean_lt_one hb t)).2
  linarith

theorem qubitObservedResponse_eq_fisher {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (qubitResponse b t / 2) ^ 2 /
        (qubitObservedProbability b t * (1 - qubitObservedProbability b t)) =
      qubitObservedResponse b t := by
  have hm : 1 - qubitMean b t ^ 2 ≠ 0 := by
    have hleft := (abs_lt.mp (abs_qubitMean_lt_one hb t)).1
    have hright := (abs_lt.mp (abs_qubitMean_lt_one hb t)).2
    have hp : 0 < (1 - qubitMean b t) * (1 + qubitMean b t) :=
      mul_pos (by linarith) (by linarith)
    have heq : (1 - qubitMean b t) * (1 + qubitMean b t) =
        1 - qubitMean b t ^ 2 := by ring
    rw [heq] at hp
    exact hp.ne'
  have hq : qubitObservedProbability b t * (1 - qubitObservedProbability b t) =
      (1 - qubitMean b t ^ 2) / 4 := by
    rw [qubitObservedProbability]
    ring
  rw [hq, qubitObservedResponse]
  field_simp [hm]
  ring

theorem tendsto_quartic_mul_qubitObservedResponse {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 4 * qubitObservedResponse b t)
      atTop (nhds (b ^ 2)) := by
  have hraw := ((tendsto_cubic_mul_qubitResponse hb).pow 2).div
    (tendsto_sq_mul_one_sub_qubitMean_sq hb) (pow_ne_zero 2 hb.ne')
  have hlimit : (b ^ 2) ^ 2 / b ^ 2 = b ^ 2 := by
    field_simp [hb.ne']
  rw [hlimit] at hraw
  change Tendsto (fun t : ℝ =>
    (t ^ 3 * qubitResponse b t) ^ 2 /
      (t ^ 2 * (1 - qubitMean b t ^ 2))) atTop (nhds (b ^ 2)) at hraw
  refine hraw.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hm : 1 - qubitMean b t ^ 2 ≠ 0 := by
    have hleft := (abs_lt.mp (abs_qubitMean_lt_one hb t)).1
    have hright := (abs_lt.mp (abs_qubitMean_lt_one hb t)).2
    nlinarith
  rw [qubitObservedResponse]
  field_simp [ht.ne', hm]

/-- Explicit cubic-plus-exponential upper tail for the full BKM response. -/
theorem qubitResponse_le_cubic_exponential_tail {b t : ℝ} (hb : 0 < b)
    (ht : 1 ≤ t) :
    qubitResponse b t ≤
      b ^ 2 / t ^ 3 + 4 * Real.exp (-(2 * t)) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htr : t ≤ qubitRadius b t :=
    (le_abs_self t).trans (abs_lt_qubitRadius hb t).le
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  have hfirst :
      b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t) ≤
        b ^ 2 / t ^ 3 := by
    calc
      b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t)
          ≤ b ^ 2 / qubitRadius b t ^ 3 := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left
              (Real.tanh_lt_one (qubitRadius b t)).le
              (by positivity : 0 ≤ b ^ 2 / qubitRadius b t ^ 3)
      _ ≤ b ^ 2 / t ^ 3 := by
            rw [div_le_div_iff₀ (pow_pos hr 3) (pow_pos ht0 3)]
            gcongr
  have hratio : t ^ 2 / qubitRadius b t ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hr)]
    nlinarith [sq_nonneg b]
  have hsecond :
      t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2 ≤
        4 * Real.exp (-(2 * t)) := by
    calc
      t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2
          ≤ 1 / Real.cosh (qubitRadius b t) ^ 2 := by
            gcongr
      _ ≤ 4 * Real.exp (-(2 * qubitRadius b t)) :=
        inv_cosh_sq_le_four_exp_neg_two hr.le
      _ ≤ 4 * Real.exp (-(2 * t)) := by
            gcongr
  rw [qubitResponse]
  exact add_le_add hfirst hsecond

end

end GaloisForLFunctions.HTGeometry
