import GaloisForLFunctions.RHTower.PrimeLogJumpMellinTrace

/-!
# The second boundary trace is `O(1/κ)`

A second integration by parts on the residual oscillatory integral of the first trace,

```text
κ ∫_A^B x^w sin (κ x) dx = A^w cos (κ A) − B^w cos (κ B) + w ∫_A^B x^{w-1} cos (κ x) dx,
```

bounds the residual by an explicit constant over `κ`.  So the first Mellin boundary trace of the
jump packet is exactly first order: the endpoint terms are the whole of the leading behaviour.
-/

namespace GaloisForLFunctions.RHTower

open Complex intervalIntegral Filter
open scoped Topology

variable {A B κ : ℝ}

/-- The primitive of the modulating sine. -/
theorem hasDerivAt_neg_cos_div (hκ : κ ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -((Real.cos (κ * t) : ℝ) : ℂ) / (κ : ℂ))
      (((Real.sin (κ * x) : ℝ) : ℂ)) x := by
  have hκ' : ((κ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  have h1 : HasDerivAt (fun t : ℝ => Real.cos (κ * t)) (-Real.sin (κ * x) * κ) x := by
    have h : HasDerivAt (fun t : ℝ => κ * t) κ x := by
      simpa using HasDerivAt.const_mul κ (hasDerivAt_id x)
    simpa [Function.comp_def] using (Real.hasDerivAt_cos (κ * x)).comp x h
  have h2 : HasDerivAt (fun t : ℝ => ((Real.cos (κ * t) : ℝ) : ℂ))
      (((-Real.sin (κ * x) * κ : ℝ) : ℂ)) x := h1.ofReal_comp
  refine ((h2.neg).div_const (κ : ℂ)).congr_deriv ?_
  push_cast
  field_simp

/-- **The second integration by parts.** -/
theorem integral_cpow_mul_sin (hA : 0 < A) (hAB : A < B) (hκ : κ ≠ 0) (w : ℂ) :
    (κ : ℂ) * ∫ x in A..B, (x : ℂ) ^ w * ((Real.sin (κ * x) : ℝ) : ℂ)
      = (A : ℂ) ^ w * ((Real.cos (κ * A) : ℝ) : ℂ)
        - (B : ℂ) ^ w * ((Real.cos (κ * B) : ℝ) : ℂ)
        + w * ∫ x in A..B, (x : ℂ) ^ (w - 1) * ((Real.cos (κ * x) : ℝ) : ℂ) := by
  have hκ' : ((κ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  have hpos : ∀ x ∈ Set.uIcc A B, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  have hu : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => ((t : ℂ)) ^ w) (w * (x : ℂ) ^ (w - 1)) x :=
    fun x hx => hasDerivAt_cpow_ofReal (hpos x hx)
  have hv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => -((Real.cos (κ * t) : ℝ) : ℂ) / (κ : ℂ))
        (((Real.sin (κ * x) : ℝ) : ℂ)) x := fun x _ => hasDerivAt_neg_cos_div hκ x
  have hu' : IntervalIntegrable (fun x : ℝ => w * (x : ℂ) ^ (w - 1)) MeasureTheory.volume A B := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (continuousAt_const.mul (continuousAt_cpow_ofReal (hpos x hx))).continuousWithinAt
  have hv' : IntervalIntegrable (fun x : ℝ => ((Real.sin (κ * x) : ℝ) : ℂ))
      MeasureTheory.volume A B := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hleft : ∫ x in A..B, ((x : ℂ) ^ w) * ((Real.sin (κ * x) : ℝ) : ℂ)
      = ((B : ℂ) ^ w * (-((Real.cos (κ * B) : ℝ) : ℂ) / (κ : ℂ))
        - (A : ℂ) ^ w * (-((Real.cos (κ * A) : ℝ) : ℂ) / (κ : ℂ)))
        - ∫ x in A..B, (w * (x : ℂ) ^ (w - 1)) * (-((Real.cos (κ * x) : ℝ) : ℂ) / (κ : ℂ)) :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [hleft]
  have hrw : (∫ x in A..B, (w * (x : ℂ) ^ (w - 1)) * (-((Real.cos (κ * x) : ℝ) : ℂ) / (κ : ℂ)))
      = (-w / (κ : ℂ)) * ∫ x in A..B, (x : ℂ) ^ (w - 1) * ((Real.cos (κ * x) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x _
    field_simp
  rw [hrw]
  field_simp
  ring

/-- A real power of a point of a positive interval is dominated by the two endpoint powers. -/
theorem rpow_le_max_endpoints (hA : 0 < A) {x r : ℝ} (h1 : A ≤ x) (h2 : x ≤ B) :
    x ^ r ≤ max (A ^ r) (B ^ r) := by
  rcases le_total 0 r with hr | hr
  · exact le_max_of_le_right (Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le hA h1)) h2 hr)
  · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos hA h1 hr)

/-- The explicit constant in the residual bound. -/
noncomputable def mellinRemainderBound (A B : ℝ) (w : ℂ) : ℝ :=
  A ^ w.re + B ^ w.re + ‖w‖ * (max (A ^ (w.re - 1)) (B ^ (w.re - 1)) * |B - A|)

/-- **The residual oscillatory integral is `O(1/κ)`.** -/
theorem norm_integral_cpow_mul_sin_le (hA : 0 < A) (hAB : A < B) (hκ : 0 < κ) (w : ℂ) :
    ‖∫ x in A..B, (x : ℂ) ^ w * ((Real.sin (κ * x) : ℝ) : ℂ)‖
      ≤ mellinRemainderBound A B w / κ := by
  have hB : 0 < B := hA.trans hAB
  have hκ' : κ ≠ 0 := ne_of_gt hκ
  have hid := integral_cpow_mul_sin hA hAB hκ' w
  have hnormA : ‖(A : ℂ) ^ w * ((Real.cos (κ * A) : ℝ) : ℂ)‖ ≤ A ^ w.re := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have h1 : ‖((Real.cos (κ * A) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have h2 : (0 : ℝ) ≤ A ^ w.re := Real.rpow_nonneg hA.le _
    nlinarith
  have hnormB : ‖(B : ℂ) ^ w * ((Real.cos (κ * B) : ℝ) : ℂ)‖ ≤ B ^ w.re := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hB]
    have h1 : ‖((Real.cos (κ * B) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have h2 : (0 : ℝ) ≤ B ^ w.re := Real.rpow_nonneg hB.le _
    nlinarith
  have hInner : ‖∫ x in A..B, (x : ℂ) ^ (w - 1) * ((Real.cos (κ * x) : ℝ) : ℂ)‖
      ≤ max (A ^ (w.re - 1)) (B ^ (w.re - 1)) * |B - A| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro x hx
    rw [Set.uIoc_of_le (le_of_lt hAB)] at hx
    have hx0 : 0 < x := hA.trans hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 : ‖((Real.cos (κ * x) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have h2 : x ^ (w - 1).re ≤ max (A ^ (w.re - 1)) (B ^ (w.re - 1)) := by
      have : (w - 1).re = w.re - 1 := by simp
      rw [this]
      exact rpow_le_max_endpoints hA hx.1.le hx.2
    have h3 : (0 : ℝ) ≤ x ^ (w - 1).re := Real.rpow_nonneg hx0.le _
    nlinarith
  have hnormw : ‖w * ∫ x in A..B, (x : ℂ) ^ (w - 1) * ((Real.cos (κ * x) : ℝ) : ℂ)‖
      ≤ ‖w‖ * (max (A ^ (w.re - 1)) (B ^ (w.re - 1)) * |B - A|) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hInner (norm_nonneg w)
  have hbig : ‖(κ : ℂ) * ∫ x in A..B, (x : ℂ) ^ w * ((Real.sin (κ * x) : ℝ) : ℂ)‖
      ≤ mellinRemainderBound A B w := by
    rw [hid, mellinRemainderBound]
    calc ‖(A : ℂ) ^ w * ((Real.cos (κ * A) : ℝ) : ℂ)
            - (B : ℂ) ^ w * ((Real.cos (κ * B) : ℝ) : ℂ)
          + w * ∫ x in A..B, (x : ℂ) ^ (w - 1) * ((Real.cos (κ * x) : ℝ) : ℂ)‖
        ≤ ‖(A : ℂ) ^ w * ((Real.cos (κ * A) : ℝ) : ℂ)
              - (B : ℂ) ^ w * ((Real.cos (κ * B) : ℝ) : ℂ)‖
            + ‖w * ∫ x in A..B, (x : ℂ) ^ (w - 1) * ((Real.cos (κ * x) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ (‖(A : ℂ) ^ w * ((Real.cos (κ * A) : ℝ) : ℂ)‖
              + ‖(B : ℂ) ^ w * ((Real.cos (κ * B) : ℝ) : ℂ)‖)
            + ‖w * ∫ x in A..B, (x : ℂ) ^ (w - 1) * ((Real.cos (κ * x) : ℝ) : ℂ)‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by gcongr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ] at hbig
  rw [le_div_iff₀ hκ, mul_comm]
  exact hbig

/-- **The residual vanishes at high frequency.** -/
theorem tendsto_integral_cpow_mul_sin (hA : 0 < A) (hAB : A < B) (w : ℂ) :
    Tendsto (fun κ : ℝ => ∫ x in A..B, (x : ℂ) ^ w * ((Real.sin (κ * x) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Tendsto (fun κ : ℝ => mellinRemainderBound A B w / κ) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  refine squeeze_zero' (Filter.Eventually.of_forall fun κ => norm_nonneg _) ?_ hmaj
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with κ hκ
  exact norm_integral_cpow_mul_sin_le hA hAB hκ w

end GaloisForLFunctions.RHTower
