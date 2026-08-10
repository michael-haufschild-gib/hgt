import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The logarithmically weighted power integral

For `0 < a < 1` the logarithmic integral of a subunit power satisfies

```text
∫_2^x t^(a-1)/log t dt ~ x^a/(a log x),      ∫_2^x t^(a-1)/log²t dt = o(x^a/log x).
```

Both follow from splitting at `x^(1-ε)`: below the split the integrand is bounded by
`t^(a-1)/log 2` and contributes `O(x^((1-ε)a))`, above it the logarithm is pinned between
`(1-ε) log x` and `log x`.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace HTGeometry

noncomputable section

/-! ## Integrability -/

theorem continuousAt_rpowDivLog {a t : ℝ} (ht : 2 ≤ t) :
    ContinuousAt (fun s : ℝ => s ^ (a - 1) / Real.log s) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  exact ContinuousAt.div (Real.continuousAt_rpow_const t (a - 1) (Or.inl (ne_of_gt ht0)))
    (Real.continuousAt_log (ne_of_gt ht0)) hlog

theorem continuousAt_rpowDivLogSq {a t : ℝ} (ht : 2 ≤ t) :
    ContinuousAt (fun s : ℝ => s ^ (a - 1) / Real.log s ^ 2) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog : Real.log t ^ 2 ≠ 0 := by positivity
  exact ContinuousAt.div (Real.continuousAt_rpow_const t (a - 1) (Or.inl (ne_of_gt ht0)))
    ((Real.continuousAt_log (ne_of_gt ht0)).pow 2) hlog

theorem two_le_of_mem_uIcc {u v t : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) (ht : t ∈ uIcc u v) :
    (2 : ℝ) ≤ t := by
  rcases le_total u v with h | h
  · rw [uIcc_of_le h] at ht
    exact le_trans hu ht.1
  · rw [uIcc_of_ge h] at ht
    exact le_trans hv ht.1

theorem intervalIntegrable_rpowDivLog (a : ℝ) {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t : ℝ => t ^ (a - 1) / Real.log t) volume u v :=
  ContinuousOn.intervalIntegrable fun _ ht =>
    (continuousAt_rpowDivLog (a := a) (two_le_of_mem_uIcc hu hv ht)).continuousWithinAt

theorem intervalIntegrable_rpowDivLogSq (a : ℝ) {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t : ℝ => t ^ (a - 1) / Real.log t ^ 2) volume u v :=
  ContinuousOn.intervalIntegrable fun _ ht =>
    (continuousAt_rpowDivLogSq (a := a) (two_le_of_mem_uIcc hu hv ht)).continuousWithinAt

theorem intervalIntegrable_rpowSubOne (a : ℝ) {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t : ℝ => t ^ (a - 1)) volume u v := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  have h2 : (2 : ℝ) ≤ t := two_le_of_mem_uIcc hu hv ht
  exact (Real.continuousAt_rpow_const t (a - 1) (Or.inl (by linarith))).continuousWithinAt

/-! ## The elementary power integral -/

theorem integral_rpow_sub_one {a : ℝ} (ha : 0 < a) (u v : ℝ) :
    (∫ t in u..v, t ^ (a - 1)) = (v ^ a - u ^ a) / a := by
  have h : a - 1 + 1 = a := by ring
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < a - 1)), h]

/-! ## The logarithmic integral -/

/-- The logarithmically weighted power integral from `2`. -/
def logRpowIntegral (a x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, t ^ (a - 1) / Real.log t

/-- The doubly logarithmically weighted power integral from `2`. -/
def logSqRpowIntegral (a x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, t ^ (a - 1) / Real.log t ^ 2

theorem logRpowIntegral_nonneg {a u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    0 ≤ ∫ t in u..v, t ^ (a - 1) / Real.log t := by
  refine intervalIntegral.integral_nonneg huv fun t ht => ?_
  have h2 : (2 : ℝ) ≤ t := le_trans hu ht.1
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hnum : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg (by linarith) _
  positivity

theorem integral_rpowDivLog_le {a u v : ℝ} (ha : 0 < a) (hu : 2 ≤ u) (huv : u ≤ v) :
    (∫ t in u..v, t ^ (a - 1) / Real.log t) ≤ (v ^ a - u ^ a) / a / Real.log u := by
  have hv : (2 : ℝ) ≤ v := le_trans hu huv
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hcmp : (∫ t in u..v, t ^ (a - 1) / Real.log t) ≤
      ∫ t in u..v, t ^ (a - 1) / Real.log u := by
    refine intervalIntegral.integral_mono_on huv (intervalIntegrable_rpowDivLog a hu hv)
      (((intervalIntegrable_rpowSubOne a hu hv).div_const _)) fun t ht => ?_
    have h2 : (2 : ℝ) ≤ t := le_trans hu ht.1
    have hnum : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg (by linarith) _
    exact div_le_div_of_nonneg_left hnum hlogu (Real.log_le_log (by linarith) ht.1)
  rwa [intervalIntegral.integral_div, integral_rpow_sub_one ha] at hcmp

theorem integral_rpowDivLog_ge {a u v : ℝ} (ha : 0 < a) (hu : 2 ≤ u) (huv : u ≤ v) :
    (v ^ a - u ^ a) / a / Real.log v ≤ ∫ t in u..v, t ^ (a - 1) / Real.log t := by
  have hv : (2 : ℝ) ≤ v := le_trans hu huv
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hcmp : (∫ t in u..v, t ^ (a - 1) / Real.log v) ≤
      ∫ t in u..v, t ^ (a - 1) / Real.log t := by
    refine intervalIntegral.integral_mono_on huv
      (((intervalIntegrable_rpowSubOne a hu hv).div_const _))
      (intervalIntegrable_rpowDivLog a hu hv) fun t ht => ?_
    have h2 : (2 : ℝ) ≤ t := le_trans hu ht.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hnum : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg (by linarith) _
    exact div_le_div_of_nonneg_left hnum hlogt (Real.log_le_log (by linarith) ht.2)
  rwa [intervalIntegral.integral_div, integral_rpow_sub_one ha] at hcmp

theorem integral_rpowDivLogSq_le {a u v : ℝ} (ha : 0 < a) (hu : 2 ≤ u) (huv : u ≤ v) :
    (∫ t in u..v, t ^ (a - 1) / Real.log t ^ 2) ≤ (v ^ a - u ^ a) / a / Real.log u ^ 2 := by
  have hv : (2 : ℝ) ≤ v := le_trans hu huv
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hcmp : (∫ t in u..v, t ^ (a - 1) / Real.log t ^ 2) ≤
      ∫ t in u..v, t ^ (a - 1) / Real.log u ^ 2 := by
    refine intervalIntegral.integral_mono_on huv (intervalIntegrable_rpowDivLogSq a hu hv)
      (((intervalIntegrable_rpowSubOne a hu hv).div_const _)) fun t ht => ?_
    have h2 : (2 : ℝ) ≤ t := le_trans hu ht.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hnum : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg (by linarith) _
    have hsq : Real.log u ^ 2 ≤ Real.log t ^ 2 := by
      have := Real.log_le_log (by linarith : (0:ℝ) < u) ht.1
      nlinarith
    exact div_le_div_of_nonneg_left hnum (by positivity) hsq
  rwa [intervalIntegral.integral_div, integral_rpow_sub_one ha] at hcmp

theorem logSqRpowIntegral_nonneg {a u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    0 ≤ ∫ t in u..v, t ^ (a - 1) / Real.log t ^ 2 := by
  refine intervalIntegral.integral_nonneg huv fun t ht => ?_
  have h2 : (2 : ℝ) ≤ t := le_trans hu ht.1
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hnum : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg (by linarith) _
  positivity

/-! ## The split -/

theorem logRpowIntegral_split {a x w : ℝ} (hw : 2 ≤ w) (hwx : w ≤ x) :
    logRpowIntegral a x =
      (∫ t in (2 : ℝ)..w, t ^ (a - 1) / Real.log t) +
        ∫ t in w..x, t ^ (a - 1) / Real.log t :=
  (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rpowDivLog a (by norm_num) hw)
      (intervalIntegrable_rpowDivLog a hw (by linarith))).symm

theorem logSqRpowIntegral_split {a x w : ℝ} (hw : 2 ≤ w) (hwx : w ≤ x) :
    logSqRpowIntegral a x =
      (∫ t in (2 : ℝ)..w, t ^ (a - 1) / Real.log t ^ 2) +
        ∫ t in w..x, t ^ (a - 1) / Real.log t ^ 2 :=
  (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rpowDivLogSq a (by norm_num) hw)
      (intervalIntegrable_rpowDivLogSq a hw (by linarith))).symm

/-! ## The asymptotics -/

private theorem tendsto_log_div_rpow {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => Real.log x / x ^ r) atTop (nhds 0) :=
  (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero

private theorem rpow_window_ge_two {ε : ℝ} (hε1 : ε < 1) :
    ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ x ^ (1 - ε) :=
  (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ε)).eventually_ge_atTop 2

private theorem rpow_window_le {ε x : ℝ} (hε0 : 0 < ε) (hx : 1 ≤ x) : x ^ (1 - ε) ≤ x := by
  have h : x ^ (1 - ε) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  rwa [Real.rpow_one] at h

private theorem sqrt_window_ge_two {x : ℝ} (hx : 4 ≤ x) : (2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
  have h : ((4 : ℝ)) ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h4 : ((4 : ℝ)) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num [Real.rpow_natCast], ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith [h4 ▸ h]

private theorem sqrt_window_le {x : ℝ} (hx : 1 ≤ x) : x ^ (1 / 2 : ℝ) ≤ x := by
  have h : x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  rwa [Real.rpow_one] at h

/-- **The logarithmic power integral is asymptotic to `x^a/(a log x)`.** -/
theorem tendsto_logRpowIntegral {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => logRpowIntegral a x * (a * Real.log x) / x ^ a) atTop (nhds 1) := by
  have hne_a : a ≠ 0 := ne_of_gt ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hne_l2 : Real.log 2 ≠ 0 := ne_of_gt hlog2
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · -- lower half: keep only the window `[√x, x]`
    intro b hb
    have hzero : Tendsto (fun x : ℝ => x ^ (-(a / 2))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have hsmall : ∀ᶠ x : ℝ in atTop, x ^ (-(a / 2)) < 1 - b :=
      hzero.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [eventually_ge_atTop (4 : ℝ), hsmall] with x hx hxs
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
    have hne_X : x ^ a ≠ 0 := ne_of_gt hXpos
    have hne_lx : Real.log x ≠ 0 := ne_of_gt hlogx
    set w : ℝ := x ^ (1 / 2 : ℝ) with hw
    have hw2 : (2 : ℝ) ≤ w := sqrt_window_ge_two hx
    have hwx : w ≤ x := sqrt_window_le (by linarith)
    have hWpos : (0 : ℝ) < w ^ a := Real.rpow_pos_of_pos (by linarith) a
    have hlow : (x ^ a - w ^ a) / a / Real.log x ≤ logRpowIntegral a x := by
      rw [logRpowIntegral_split hw2 hwx]
      have h1 : 0 ≤ ∫ t in (2 : ℝ)..w, t ^ (a - 1) / Real.log t :=
        logRpowIntegral_nonneg (by norm_num) hw2
      have h2 := integral_rpowDivLog_ge (a := a) ha hw2 hwx
      linarith
    have hratio : w ^ a / x ^ a = x ^ (-(a / 2)) := by
      rw [hw, ← Real.rpow_mul hx0.le, ← Real.rpow_sub hx0]
      congr 1
      ring
    have hmul : (x ^ a - w ^ a) / a / Real.log x * (a * Real.log x) ≤
        logRpowIntegral a x * (a * Real.log x) :=
      mul_le_mul_of_nonneg_right hlow (by positivity)
    have hval : (x ^ a - w ^ a) / a / Real.log x * (a * Real.log x) = x ^ a - w ^ a := by
      field_simp
    rw [hval] at hmul
    have hstep : (x ^ a - w ^ a) / x ^ a ≤ logRpowIntegral a x * (a * Real.log x) / x ^ a :=
      div_le_div_of_nonneg_right hmul hXpos.le
    have hsplit : (x ^ a - w ^ a) / x ^ a = 1 - x ^ (-(a / 2)) := by
      rw [sub_div, div_self hne_X, hratio]
    rw [hsplit] at hstep
    linarith
  · -- upper half: split at `x^(1-ε)`
    intro b hb
    set ε : ℝ := (1 - 1 / b) / 2 with hε
    have hb0 : (0 : ℝ) < b := by linarith
    have hbinv : 1 / b < 1 := by
      rw [div_lt_one hb0]
      exact hb
    have hbpos : (0 : ℝ) < 1 / b := by positivity
    have hε0 : 0 < ε := by
      rw [hε]
      linarith
    have hε1 : ε < 1 := by
      rw [hε]
      linarith
    have hone : (0 : ℝ) < 1 - ε := by linarith
    have hne_e : (1 : ℝ) - ε ≠ 0 := ne_of_gt hone
    have hbound : 1 / (1 - ε) < b := by
      rw [div_lt_iff₀ hone, hε]
      have hbb : 1 / b * b = 1 := by field_simp
      nlinarith
    have hzero : Tendsto (fun x : ℝ => Real.log x / x ^ (ε * a)) atTop (nhds 0) :=
      tendsto_log_div_rpow (by positivity)
    have hsmall : ∀ᶠ x : ℝ in atTop,
        Real.log x / x ^ (ε * a) / Real.log 2 < b - 1 / (1 - ε) := by
      have hdiv : Tendsto (fun x : ℝ => Real.log x / x ^ (ε * a) / Real.log 2) atTop (nhds 0) := by
        have h := hzero.div_const (Real.log 2)
        rwa [zero_div] at h
      exact hdiv.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [eventually_ge_atTop (2 : ℝ), rpow_window_ge_two hε1, hsmall]
      with x hx hw2 hxs
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hne_lx : Real.log x ≠ 0 := ne_of_gt hlogx
    have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
    have hne_X : x ^ a ≠ 0 := ne_of_gt hXpos
    set w : ℝ := x ^ (1 - ε) with hw
    have hwx : w ≤ x := rpow_window_le hε0 (by linarith)
    have hWpos : (0 : ℝ) < w ^ a := Real.rpow_pos_of_pos (by linarith) a
    have hlogw : Real.log w = (1 - ε) * Real.log x := by
      rw [hw, Real.log_rpow hx0]
    have hlogwpos : 0 < Real.log w := by
      rw [hlogw]
      positivity
    have hhead : (∫ t in (2 : ℝ)..w, t ^ (a - 1) / Real.log t) ≤ w ^ a / a / Real.log 2 := by
      have h := integral_rpowDivLog_le (a := a) ha (le_refl (2 : ℝ)) hw2
      have hpos : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
      have hmono : (w ^ a - (2 : ℝ) ^ a) / a / Real.log 2 ≤ w ^ a / a / Real.log 2 :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) ha.le) hlog2.le
      linarith
    have htail : (∫ t in w..x, t ^ (a - 1) / Real.log t) ≤ x ^ a / a / Real.log w := by
      have h := integral_rpowDivLog_le (a := a) ha hw2 hwx
      have hmono : (x ^ a - w ^ a) / a / Real.log w ≤ x ^ a / a / Real.log w :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) ha.le) hlogwpos.le
      linarith
    have hJ : logRpowIntegral a x ≤ w ^ a / a / Real.log 2 + x ^ a / a / Real.log w := by
      rw [logRpowIntegral_split hw2 hwx]
      linarith
    have hmul : logRpowIntegral a x * (a * Real.log x) ≤
        (w ^ a / a / Real.log 2 + x ^ a / a / Real.log w) * (a * Real.log x) :=
      mul_le_mul_of_nonneg_right hJ (by positivity)
    have hstep : logRpowIntegral a x * (a * Real.log x) / x ^ a ≤
        (w ^ a / a / Real.log 2 + x ^ a / a / Real.log w) * (a * Real.log x) / x ^ a :=
      div_le_div_of_nonneg_right hmul hXpos.le
    have hratio : w ^ a / x ^ a = (x ^ (ε * a))⁻¹ := by
      rw [hw, ← Real.rpow_mul hx0.le, ← Real.rpow_sub hx0, ← Real.rpow_neg hx0.le]
      congr 1
      ring
    have hEpos : (0 : ℝ) < x ^ (ε * a) := Real.rpow_pos_of_pos hx0 _
    have hfinal : (w ^ a / a / Real.log 2 + x ^ a / a / Real.log w) * (a * Real.log x) / x ^ a
        = w ^ a / x ^ a * Real.log x / Real.log 2 + 1 / (1 - ε) := by
      rw [hlogw, add_mul, add_div]
      congr 1
      · field_simp
      · field_simp
    rw [hfinal, hratio] at hstep
    have hconv : (x ^ (ε * a))⁻¹ * Real.log x / Real.log 2
        = Real.log x / x ^ (ε * a) / Real.log 2 := by
      field_simp
    rw [hconv] at hstep
    linarith

/-- **The doubly logarithmic power integral is of smaller order.** -/
theorem tendsto_logSqRpowIntegral {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => logSqRpowIntegral a x * Real.log x / x ^ a) atTop (nhds 0) := by
  have hne_a : a ≠ 0 := ne_of_gt ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hne_l2 : Real.log 2 ≠ 0 := ne_of_gt hlog2
  have hmajor : Tendsto (fun x : ℝ =>
      Real.log x / x ^ (a / 2) / (a * Real.log 2 ^ 2) + 4 / (a * Real.log x)) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (a / 2) / (a * Real.log 2 ^ 2)) atTop
        (nhds 0) := by
      have h := (tendsto_log_div_rpow (r := a / 2) (by linarith)).div_const (a * Real.log 2 ^ 2)
      rwa [zero_div] at h
    have h2 : Tendsto (fun x : ℝ => 4 / (a * Real.log x)) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds (Filter.Tendsto.const_mul_atTop ha Real.tendsto_log_atTop)
    have h := h1.add h2
    rwa [add_zero] at h
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hK : 0 ≤ logSqRpowIntegral a x :=
      logSqRpowIntegral_nonneg (by norm_num) (by linarith)
    positivity
  · filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
    have hne_X : x ^ a ≠ 0 := ne_of_gt hXpos
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hne_lx : Real.log x ≠ 0 := ne_of_gt hlogx
    set w : ℝ := x ^ (1 / 2 : ℝ) with hw
    have hw2 : (2 : ℝ) ≤ w := sqrt_window_ge_two (by linarith)
    have hwx : w ≤ x := sqrt_window_le (by linarith)
    have hWpos : (0 : ℝ) < w ^ a := Real.rpow_pos_of_pos (by linarith) a
    have hlogw : Real.log w = (1 / 2 : ℝ) * Real.log x := by
      rw [hw, Real.log_rpow hx0]
    have hlogwpos : 0 < Real.log w := by
      rw [hlogw]
      positivity
    have hhead : (∫ t in (2 : ℝ)..w, t ^ (a - 1) / Real.log t ^ 2) ≤
        w ^ a / a / Real.log 2 ^ 2 := by
      have h := integral_rpowDivLogSq_le (a := a) ha (le_refl (2 : ℝ)) hw2
      have hpos : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
      have hmono : (w ^ a - (2 : ℝ) ^ a) / a / Real.log 2 ^ 2 ≤ w ^ a / a / Real.log 2 ^ 2 :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) ha.le)
          (by positivity)
      linarith
    have htail : (∫ t in w..x, t ^ (a - 1) / Real.log t ^ 2) ≤ x ^ a / a / Real.log w ^ 2 := by
      have h := integral_rpowDivLogSq_le (a := a) ha hw2 hwx
      have hmono : (x ^ a - w ^ a) / a / Real.log w ^ 2 ≤ x ^ a / a / Real.log w ^ 2 :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) ha.le)
          (by positivity)
      linarith
    have hK : logSqRpowIntegral a x ≤ w ^ a / a / Real.log 2 ^ 2 + x ^ a / a / Real.log w ^ 2 := by
      rw [logSqRpowIntegral_split hw2 hwx]
      linarith
    have hmul : logSqRpowIntegral a x * Real.log x ≤
        (w ^ a / a / Real.log 2 ^ 2 + x ^ a / a / Real.log w ^ 2) * Real.log x :=
      mul_le_mul_of_nonneg_right hK hlogx.le
    have hstep : logSqRpowIntegral a x * Real.log x / x ^ a ≤
        (w ^ a / a / Real.log 2 ^ 2 + x ^ a / a / Real.log w ^ 2) * Real.log x / x ^ a :=
      div_le_div_of_nonneg_right hmul hXpos.le
    have hratio : w ^ a / x ^ a = (x ^ (a / 2))⁻¹ := by
      rw [hw, ← Real.rpow_mul hx0.le, ← Real.rpow_sub hx0, ← Real.rpow_neg hx0.le]
      congr 1
      ring
    have hEpos : (0 : ℝ) < x ^ (a / 2) := Real.rpow_pos_of_pos hx0 _
    have hfinal : (w ^ a / a / Real.log 2 ^ 2 + x ^ a / a / Real.log w ^ 2) * Real.log x / x ^ a
        = w ^ a / x ^ a * Real.log x / (a * Real.log 2 ^ 2) + 4 / (a * Real.log x) := by
      rw [hlogw, add_mul, add_div]
      congr 1
      · field_simp
      · field_simp
        ring
    rw [hfinal, hratio] at hstep
    have hconv : (x ^ (a / 2))⁻¹ * Real.log x / (a * Real.log 2 ^ 2)
        = Real.log x / x ^ (a / 2) / (a * Real.log 2 ^ 2) := by
      field_simp
    rw [hconv] at hstep
    exact hstep

/-- **A vanishing weight against a logarithmically damped power kernel contributes nothing.**  If
`g → 0` and the kernel is dominated by `C·t^(a-1)/log t`, then the weighted integral is
`o(x^a/log x)`.  Splitting at a height where `|g| ≤ δ` bounds the tail by `Cδ` times the
logarithmic power integral, whose normalization tends to one, while the head is a constant. -/
theorem tendsto_logKernelRemainder {a : ℝ} (ha0 : 0 < a) {C : ℝ} (hC0 : 0 ≤ C) {g K : ℝ → ℝ}
    (hgt : Tendsto g atTop (nhds 0))
    (hKbd : ∀ t : ℝ, 2 ≤ t → |K t| ≤ C * (t ^ (a - 1) / Real.log t))
    (hgint : ∀ x : ℝ, 2 ≤ x → IntervalIntegrable (fun t : ℝ => g t * K t) volume 2 x) :
    Tendsto (fun x : ℝ => (∫ t in (2 : ℝ)..x, g t * K t) * (a * Real.log x) / x ^ a) atTop
      (nhds 0) := by
  have hJ := tendsto_logRpowIntegral ha0
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hCC : (0 : ℝ) < 4 * (C + 1) := by linarith
  set δ : ℝ := ε / (4 * (C + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε hCC
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (NormedAddGroup.tendsto_nhds_zero.mp hgt δ hδ0)
  set T : ℝ := max T₀ 2 with hT
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hTg : ∀ t : ℝ, T ≤ t → |g t| ≤ δ := by
    intro t ht
    have h := hT₀ t (le_trans (le_max_left _ _) ht)
    rw [Real.norm_eq_abs] at h
    exact h.le
  have hCδ0 : (0 : ℝ) ≤ C * δ := mul_nonneg hC0 hδ0.le
  set A : ℝ := ∫ t in (2 : ℝ)..T, g t * K t with hA
  have hhead : Tendsto (fun x : ℝ => |A| * (a * Real.log x) / x ^ a) atTop (nhds 0) := by
    have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
    have h := hlogdiv.const_mul (|A| * a)
    rw [mul_zero] at h
    refine h.congr fun x => ?_
    ring
  have hsmallhead : ∀ᶠ x : ℝ in atTop, |A| * (a * Real.log x) / x ^ a < ε / 2 :=
    (NormedAddGroup.tendsto_nhds_zero.mp hhead (ε / 2) (by linarith)).mono fun x hx => by
      rw [Real.norm_eq_abs] at hx
      exact lt_of_le_of_lt (le_abs_self _) hx
  have hJbound : ∀ᶠ x : ℝ in atTop, logRpowIntegral a x * (a * Real.log x) / x ^ a < 2 :=
    hJ.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop T, hsmallhead, hJbound] with x hx hxhead hxJ
  have hx2 : (2 : ℝ) ≤ x := le_trans hT2 hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hsplit : (∫ t in (2 : ℝ)..x, g t * K t) = A + ∫ t in T..x, g t * K t := by
    rw [hA]
    exact (intervalIntegral.integral_add_adjacent_intervals (hgint T hT2)
      ((hgint x hx2).mono_set (by
        rw [uIcc_of_le hx, uIcc_of_le hx2]
        exact Icc_subset_Icc hT2 le_rfl))).symm
  have hmajor : IntervalIntegrable
      (fun t : ℝ => C * δ * (t ^ (a - 1) / Real.log t)) volume T x :=
    (intervalIntegrable_rpowDivLog a hT2 hx2).const_mul _
  have htailint : IntervalIntegrable (fun t : ℝ => g t * K t) volume T x :=
    (hgint x hx2).mono_set (by
      rw [uIcc_of_le hx, uIcc_of_le hx2]
      exact Icc_subset_Icc hT2 le_rfl)
  have hpt : ∀ t ∈ Icc T x, |g t * K t| ≤ C * δ * (t ^ (a - 1) / Real.log t) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := le_trans hT2 ht.1
    rw [abs_mul]
    calc |g t| * |K t|
        ≤ δ * (C * (t ^ (a - 1) / Real.log t)) :=
          mul_le_mul (hTg t ht.1) (hKbd t ht2) (abs_nonneg _) hδ0.le
      _ = C * δ * (t ^ (a - 1) / Real.log t) := by ring
  have hupper : (∫ t in T..x, g t * K t) ≤
      ∫ t in T..x, C * δ * (t ^ (a - 1) / Real.log t) :=
    intervalIntegral.integral_mono_on hx htailint hmajor fun t ht =>
      le_trans (le_abs_self _) (hpt t ht)
  have hlower : (∫ t in T..x, -(C * δ * (t ^ (a - 1) / Real.log t))) ≤
      ∫ t in T..x, g t * K t :=
    intervalIntegral.integral_mono_on hx hmajor.neg htailint fun t ht =>
      neg_le_of_abs_le (hpt t ht)
  rw [intervalIntegral.integral_neg] at hlower
  have habs : |∫ t in T..x, g t * K t| ≤
      ∫ t in T..x, C * δ * (t ^ (a - 1) / Real.log t) := abs_le.mpr ⟨hlower, hupper⟩
  have hval : (∫ t in T..x, C * δ * (t ^ (a - 1) / Real.log t)) ≤
      C * δ * logRpowIntegral a x := by
    rw [intervalIntegral.integral_const_mul]
    have hhd : 0 ≤ ∫ t in (2 : ℝ)..T, t ^ (a - 1) / Real.log t :=
      logRpowIntegral_nonneg (le_refl (2 : ℝ)) hT2
    have hsp : logRpowIntegral a x =
        (∫ t in (2 : ℝ)..T, t ^ (a - 1) / Real.log t) + ∫ t in T..x, t ^ (a - 1) / Real.log t :=
      logRpowIntegral_split hT2 hx
    nlinarith [hhd, hsp]
  have hEbound : |∫ t in (2 : ℝ)..x, g t * K t| ≤ |A| + C * δ * logRpowIntegral a x := by
    rw [hsplit]
    linarith [habs, hval, abs_add_le A (∫ t in T..x, g t * K t)]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hXpos,
    abs_of_pos (show (0 : ℝ) < a * Real.log x by positivity)]
  have hstep : |∫ t in (2 : ℝ)..x, g t * K t| * (a * Real.log x) / x ^ a ≤
      (|A| + C * δ * logRpowIntegral a x) * (a * Real.log x) / x ^ a := by
    have h := mul_le_mul_of_nonneg_right hEbound (show (0 : ℝ) ≤ a * Real.log x by positivity)
    exact div_le_div_of_nonneg_right h hXpos.le
  have hexpand : (|A| + C * δ * logRpowIntegral a x) * (a * Real.log x) / x ^ a
      = |A| * (a * Real.log x) / x ^ a
        + C * δ * (logRpowIntegral a x * (a * Real.log x) / x ^ a) := by
    ring
  rw [hexpand] at hstep
  have hfinal : C * δ * (logRpowIntegral a x * (a * Real.log x) / x ^ a) ≤ ε / 2 := by
    have h1 : C * δ * (logRpowIntegral a x * (a * Real.log x) / x ^ a) ≤ C * δ * 2 :=
      mul_le_mul_of_nonneg_left hxJ.le hCδ0
    have hδmul : δ * (4 * (C + 1)) = ε := by
      rw [hδ, div_mul_cancel₀ _ (ne_of_gt hCC)]
    have h2 : C * δ * 2 ≤ ε / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hδ0, hC0, hδmul]
    linarith
  linarith

end

end HTGeometry
