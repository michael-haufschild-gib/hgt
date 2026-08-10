import GaloisForLFunctions.RHTower.GaussComponentVerticalPhase

/-!
# The finite-shift ratio law of a Gauss component

Over a fixed forward window the exact Gauss component is asymptotically a pure rotation by its
universal logarithmic clock:

`ρ(t + h) / ρ(t) - exp(h · I/m · log(t/2π)) → 0`  as `t → ∞`.

Two inputs are combined.  The exact finite-shift transport writes the ratio as the exponential of
the accumulated logarithmic derivative; the clock approximation says that the accumulated
derivative differs from the accumulated clock by a vanishing amount.  What remains is that the
clock itself is slowly varying: on `[t, t + h]` the increment `log(x/t)` is squeezed between `0`
and `h/t`, so the accumulated clock differs from `h · clock(t)` by at most `h²/(m t)`.
-/

namespace RHTower

open Filter Topology MeasureTheory

noncomputable section

/-! ## The clock is slowly varying -/

theorem continuousOn_log_div_two_pi {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    ContinuousOn (fun x : ℝ => Real.log (x / (2 * Real.pi))) (Set.uIcc t (t + h)) := by
  intro x hx
  rw [Set.uIcc_of_le (by linarith)] at hx
  have hxpos : 0 < x := lt_of_lt_of_le ht hx.1
  have hne : x / (2 * Real.pi) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    positivity
  have hdiv : ContinuousAt (fun y : ℝ => y / (2 * Real.pi)) x := by fun_prop
  exact (hdiv.log hne).continuousWithinAt

theorem intervalIntegrable_log_div_two_pi {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    IntervalIntegrable (fun x : ℝ => Real.log (x / (2 * Real.pi))) volume t (t + h) :=
  (continuousOn_log_div_two_pi ht hh).intervalIntegrable

/-- On a forward window the logarithmic increment is squeezed between `0` and `h/t`. -/
theorem log_div_self_bounds {t h x : ℝ} (ht : 0 < t) (hh : 0 ≤ h)
    (hx : x ∈ Set.uIcc t (t + h)) :
    0 ≤ Real.log (x / (2 * Real.pi)) - Real.log (t / (2 * Real.pi)) ∧
      Real.log (x / (2 * Real.pi)) - Real.log (t / (2 * Real.pi)) ≤ h / t := by
  rw [Set.uIcc_of_le (by linarith)] at hx
  have hxpos : 0 < x := lt_of_lt_of_le ht hx.1
  have htwo : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsplit : Real.log (x / (2 * Real.pi)) - Real.log (t / (2 * Real.pi))
      = Real.log (x / t) := by
    rw [Real.log_div hxpos.ne' htwo.ne', Real.log_div ht.ne' htwo.ne',
      Real.log_div hxpos.ne' ht.ne']
    ring
  rw [hsplit]
  constructor
  · exact Real.log_nonneg ((one_le_div ht).mpr hx.1)
  · have hle : Real.log (x / t) ≤ x / t - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hxpos ht)
    have hxle : x / t - 1 ≤ h / t := by
      rw [div_sub_one ht.ne', div_le_div_iff_of_pos_right ht]
      linarith [hx.2]
    linarith

/-- **The accumulated clock is the clock times the window length, up to `h²/t`.** -/
theorem abs_intervalIntegral_log_sub_le {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    |(∫ x in t..(t + h), Real.log (x / (2 * Real.pi))) -
      h * Real.log (t / (2 * Real.pi))| ≤ h * (h / t) := by
  have hle : t ≤ t + h := by linarith
  have hconst : (∫ _x in t..(t + h), Real.log (t / (2 * Real.pi)))
      = h * Real.log (t / (2 * Real.pi)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring_nf
  have hsub : (∫ x in t..(t + h), Real.log (x / (2 * Real.pi))) -
      h * Real.log (t / (2 * Real.pi))
      = ∫ x in t..(t + h),
          (Real.log (x / (2 * Real.pi)) - Real.log (t / (2 * Real.pi))) := by
    rw [← hconst, ← intervalIntegral.integral_sub
      (intervalIntegrable_log_div_two_pi ht hh) intervalIntegrable_const]
  rw [hsub]
  have hnonneg : 0 ≤ ∫ x in t..(t + h),
      (Real.log (x / (2 * Real.pi)) - Real.log (t / (2 * Real.pi))) := by
    apply intervalIntegral.integral_nonneg hle
    intro x hx
    exact (log_div_self_bounds ht hh (by
      rw [Set.uIcc_of_le hle]; exact hx)).1
  have hupper : (∫ x in t..(t + h),
      (Real.log (x / (2 * Real.pi)) - Real.log (t / (2 * Real.pi)))) ≤ h * (h / t) := by
    have hbound := intervalIntegral.integral_mono_on hle
      ((intervalIntegrable_log_div_two_pi ht hh).sub intervalIntegrable_const)
      (intervalIntegrable_const (c := h / t))
      (fun x hx => (log_div_self_bounds ht hh (by
        rw [Set.uIcc_of_le hle]; exact hx)).2)
    calc
      (∫ x in t..(t + h),
          (Real.log (x / (2 * Real.pi)) - Real.log (t / (2 * Real.pi))))
          ≤ ∫ _x in t..(t + h), h / t := hbound
      _ = h * (h / t) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring_nf
  rw [abs_of_nonneg hnonneg]
  exact hupper

theorem tendsto_intervalIntegral_log_sub_zero {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (fun t : ℝ =>
      (∫ x in t..(t + h), Real.log (x / (2 * Real.pi))) -
        h * Real.log (t / (2 * Real.pi))) atTop (nhds 0) := by
  have hbound : Tendsto (fun t : ℝ => h * (h / t)) atTop (nhds 0) := by
    have := tendsto_const_nhds (x := h * h) (f := atTop (α := ℝ))
    simpa [mul_div_assoc] using this.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simpa [Real.norm_eq_abs] using abs_intervalIntegral_log_sub_le ht hh

/-! ## Real and imaginary parts of the clock -/

theorem gaussComponentVerticalClock_eq (m : ℕ) (x : ℝ) :
    gaussComponentVerticalClock m x =
      ((Real.log (x / (2 * Real.pi)) / (m : ℝ) : ℝ) : ℂ) * Complex.I := by
  rw [gaussComponentVerticalClock]
  push_cast
  ring

@[simp] theorem gaussComponentVerticalClock_re (m : ℕ) (x : ℝ) :
    (gaussComponentVerticalClock m x).re = 0 := by
  rw [gaussComponentVerticalClock_eq]
  simp

@[simp] theorem gaussComponentVerticalClock_im (m : ℕ) (x : ℝ) :
    (gaussComponentVerticalClock m x).im = Real.log (x / (2 * Real.pi)) / (m : ℝ) := by
  rw [gaussComponentVerticalClock_eq]
  simp

theorem continuousOn_gaussComponentVerticalClock (m : ℕ) {t h : ℝ}
    (ht : 0 < t) (hh : 0 ≤ h) :
    ContinuousOn (fun x : ℝ => gaussComponentVerticalClock m x) (Set.uIcc t (t + h)) := by
  have hlog := continuousOn_log_div_two_pi ht hh
  simp only [gaussComponentVerticalClock_eq]
  exact (Complex.continuous_ofReal.comp_continuousOn (hlog.div_const _)).mul continuousOn_const

/-! ## The accumulated clock over a forward window -/

/-- Accumulated universal clock over a forward window. -/
def gaussComponentVerticalAccumulatedClock (m : ℕ) (t h : ℝ) : ℂ :=
  ((∫ x in t..(t + h), (gaussComponentVerticalClock m x).re : ℝ) : ℂ) +
    ((∫ x in t..(t + h), (gaussComponentVerticalClock m x).im : ℝ) : ℂ) * Complex.I

theorem gaussComponentVerticalAccumulatedClock_eq (m : ℕ) (t h : ℝ) :
    gaussComponentVerticalAccumulatedClock m t h =
      (((∫ x in t..(t + h), Real.log (x / (2 * Real.pi))) / (m : ℝ) : ℝ) : ℂ) *
        Complex.I := by
  rw [gaussComponentVerticalAccumulatedClock]
  simp only [gaussComponentVerticalClock_re, gaussComponentVerticalClock_im,
    intervalIntegral.integral_zero, Complex.ofReal_zero, zero_add]
  congr 2
  rw [intervalIntegral.integral_div]

/-- **The accumulated clock is the pointwise clock times the window length, asymptotically.** -/
theorem gaussComponentVerticalAccumulatedClock_sub_tendsto_zero
    {m : ℕ} (hm : 1 ≤ m) {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (fun t : ℝ =>
      gaussComponentVerticalAccumulatedClock m t h -
        (h : ℂ) * gaussComponentVerticalClock m t) atTop (nhds 0) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hbase := tendsto_intervalIntegral_log_sub_zero hh
  have hscaled : Tendsto (fun t : ℝ =>
      ((((∫ x in t..(t + h), Real.log (x / (2 * Real.pi))) -
        h * Real.log (t / (2 * Real.pi))) / (m : ℝ) : ℝ) : ℂ) * Complex.I)
      atTop (nhds 0) := by
    have hdiv : Tendsto (fun t : ℝ =>
        (((∫ x in t..(t + h), Real.log (x / (2 * Real.pi))) -
          h * Real.log (t / (2 * Real.pi))) / (m : ℝ))) atTop (nhds 0) := by
      simpa using hbase.div_const (m : ℝ)
    have hcast : Tendsto (fun t : ℝ =>
        ((((∫ x in t..(t + h), Real.log (x / (2 * Real.pi))) -
          h * Real.log (t / (2 * Real.pi))) / (m : ℝ) : ℝ) : ℂ)) atTop (nhds 0) := by
      have hcomp := Complex.continuous_ofReal.continuousAt.tendsto.comp hdiv
      simpa only [Function.comp_def, Complex.ofReal_zero] using hcomp
    simpa only [zero_mul] using hcast.mul_const Complex.I
  refine hscaled.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [gaussComponentVerticalAccumulatedClock_eq m t h, gaussComponentVerticalClock_eq]
  push_cast
  ring

/-! ## The ratio law -/

/-- Accumulated exact logarithmic derivative over a forward window. -/
def gaussComponentVerticalAccumulatedLogDeriv {m : ℕ} (k : Fin m) (t h : ℝ) : ℂ :=
  ((∫ x in t..(t + h), (gaussComponentVerticalLogDeriv k x).re : ℝ) : ℂ) +
    ((∫ x in t..(t + h), (gaussComponentVerticalLogDeriv k x).im : ℝ) : ℂ) * Complex.I

theorem intervalIntegrable_gaussComponentVerticalLogDeriv_re
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    IntervalIntegrable (fun x : ℝ => (gaussComponentVerticalLogDeriv k x).re)
      volume t (t + h) := by
  have hsub : Set.uIcc t (t + h) ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro x hx
    exact lt_of_lt_of_le ht hx.1
  exact (Complex.continuous_re.comp_continuousOn
    ((continuousOn_gaussComponentVerticalLogDeriv_pos hm k).mono hsub)).intervalIntegrable

theorem intervalIntegrable_gaussComponentVerticalLogDeriv_im
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    IntervalIntegrable (fun x : ℝ => (gaussComponentVerticalLogDeriv k x).im)
      volume t (t + h) := by
  have hsub : Set.uIcc t (t + h) ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro x hx
    exact lt_of_lt_of_le ht hx.1
  exact (Complex.continuous_im.comp_continuousOn
    ((continuousOn_gaussComponentVerticalLogDeriv_pos hm k).mono hsub)).intervalIntegrable

/-- The accumulated derivative splits as accumulated clock plus accumulated error. -/
theorem gaussComponentVerticalAccumulatedLogDeriv_eq
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    gaussComponentVerticalAccumulatedLogDeriv k t h =
      gaussComponentVerticalAccumulatedClock m t h +
        gaussComponentVerticalAccumulatedError k t h := by
  have hclockRe : ContinuousOn (fun x : ℝ => (gaussComponentVerticalClock m x).re)
      (Set.uIcc t (t + h)) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_gaussComponentVerticalClock m ht hh)
  have hclockIm : ContinuousOn (fun x : ℝ => (gaussComponentVerticalClock m x).im)
      (Set.uIcc t (t + h)) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_gaussComponentVerticalClock m ht hh)
  have hre : (∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).re)
      = (∫ x in t..(t + h), (gaussComponentVerticalLogDeriv k x).re) -
        (∫ x in t..(t + h), (gaussComponentVerticalClock m x).re) := by
    rw [← intervalIntegral.integral_sub
      (intervalIntegrable_gaussComponentVerticalLogDeriv_re hm k ht hh)
      hclockRe.intervalIntegrable]
    rfl
  have him : (∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).im)
      = (∫ x in t..(t + h), (gaussComponentVerticalLogDeriv k x).im) -
        (∫ x in t..(t + h), (gaussComponentVerticalClock m x).im) := by
    rw [← intervalIntegral.integral_sub
      (intervalIntegrable_gaussComponentVerticalLogDeriv_im hm k ht hh)
      hclockIm.intervalIntegrable]
    rfl
  rw [gaussComponentVerticalAccumulatedLogDeriv, gaussComponentVerticalAccumulatedClock,
    gaussComponentVerticalAccumulatedError, hre, him]
  push_cast
  ring

/-- **Finite-shift ratio law.**  Over a fixed forward window the exact Gauss component is
asymptotically the pure rotation prescribed by its universal clock. -/
theorem gaussComponentVerticalValue_ratio_sub_clock_tendsto_zero
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (fun t : ℝ =>
      gaussComponentVerticalValue k (t + h) / gaussComponentVerticalValue k t -
        Complex.exp ((h : ℂ) * gaussComponentVerticalClock m t)) atTop (nhds 0) := by
  have hdiff : Tendsto (fun t : ℝ =>
      gaussComponentVerticalAccumulatedLogDeriv k t h -
        (h : ℂ) * gaussComponentVerticalClock m t) atTop (nhds 0) := by
    have hclock := gaussComponentVerticalAccumulatedClock_sub_tendsto_zero hm (h := h) hh
    have herr := gaussComponentVerticalAccumulatedError_tendsto_zero hm k hh
    have hsum := hclock.add herr
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [gaussComponentVerticalAccumulatedLogDeriv_eq hm k ht hh]
    ring
  have hexp : Tendsto (fun t : ℝ =>
      Complex.exp (gaussComponentVerticalAccumulatedLogDeriv k t h -
        (h : ℂ) * gaussComponentVerticalClock m t) - 1) atTop (nhds 0) := by
    have hcomp := (Complex.continuous_exp.tendsto 0).comp hdiff
    simp only [Function.comp_def, Complex.exp_zero] at hcomp
    have hconst : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using hcomp.sub hconst
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (fun t : ℝ => ‖Complex.exp ((h : ℂ) * gaussComponentVerticalClock m t)‖) := by
    refine ⟨1, ?_⟩
    change ∀ᶠ t : ℝ in atTop,
      ‖Complex.exp ((h : ℂ) * gaussComponentVerticalClock m t)‖ ≤ 1
    filter_upwards with t
    rw [Complex.norm_exp]
    have hre : ((h : ℂ) * gaussComponentVerticalClock m t).re = 0 := by
      simp [Complex.mul_re]
    rw [hre]
    simp
  have hzero := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hexp hbounded
  refine hzero.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hratio : gaussComponentVerticalValue k (t + h) / gaussComponentVerticalValue k t
      = Complex.exp (gaussComponentVerticalAccumulatedLogDeriv k t h) := by
    rw [gaussComponentVerticalAccumulatedLogDeriv,
      gaussComponentVerticalValue_add_div_eq_exp_integral_logDeriv hm k ht hh]
  rw [hratio]
  simp only [Pi.mul_apply, smul_eq_mul]
  rw [sub_mul, one_mul, ← Complex.exp_add, sub_add_cancel]

end

end RHTower
