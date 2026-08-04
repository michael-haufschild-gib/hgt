import GaloisForLFunctions.RHTower.BesselJZeroPhase
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric

/-!
# A second solution of Bessel's equation of order zero

Bessel's equation has a second solution independent of `J_0`, and it is needed for the Green kernel of
any pole-uniform comparison.  Instead of importing the classical `Y_0` — whose usual definitions are
either a Frobenius series or a conditionally convergent integral — this file builds an explicit second
solution out of *absolutely convergent* data:

```text
K(u) = (pi/4) log u · J_0(u) + M(u),      M(u) = int_0^(pi/2) cos(u cos θ) log(sin θ) dθ.
```

The weight `log (sin θ)` is integrable, so `M` is an honest Bochner integral and differentiation under
the integral sign applies with the dominating function `|log (sin θ)|`.

* `besselJ0_cos_form`, `besselJ0Deriv_cos_form` — the cosine forms of the representation and of its
  derivative, obtained from the sine forms by the reflection `θ ↦ pi/2 - θ`.
* `besselM`, `besselMDeriv`, `besselMSecondDeriv`, `hasDerivAt_besselM`, `hasDerivAt_besselMDeriv` —
  the log-weighted integral and its two derivatives.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

/-! ## The cosine forms -/

theorem besselJ0_cos_form (u : ℝ) :
    besselJ0 u = 2 / Real.pi * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.cos θ) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => Real.cos (u * Real.sin θ)) (Real.pi / 2) (a := 0) (b := Real.pi / 2)
  have h1 : Real.pi / 2 - Real.pi / 2 = (0 : ℝ) := by ring
  have h2 : Real.pi / 2 - 0 = Real.pi / 2 := by ring
  rw [h1, h2] at h
  rw [besselJ0_eq_two_div_pi_mul, ← h]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Real.sin_pi_div_two_sub]

theorem besselJ0Deriv_cos_form (u : ℝ) :
    besselJ0Deriv u
      = -(2 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 2),
          Real.cos θ * Real.sin (u * Real.cos θ) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => Real.sin θ * Real.sin (u * Real.sin θ)) (Real.pi / 2) (a := 0) (b := Real.pi / 2)
  have h1 : Real.pi / 2 - Real.pi / 2 = (0 : ℝ) := by ring
  have h2 : Real.pi / 2 - 0 = Real.pi / 2 := by ring
  rw [h1, h2] at h
  rw [besselJ0Deriv_eq_two_div_pi_mul, ← h]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Real.sin_pi_div_two_sub]

/-! ## The log-weighted integral and its derivatives -/

/-- The log-weighted cosine integral of Neumann's second solution. -/
def besselM (u : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.cos θ) * Real.log (Real.sin θ)

/-- Its derivative. -/
def besselMDeriv (u : ℝ) : ℝ :=
  -∫ θ in (0 : ℝ)..(Real.pi / 2),
    Real.cos θ * Real.sin (u * Real.cos θ) * Real.log (Real.sin θ)

/-- Its second derivative. -/
def besselMSecondDeriv (u : ℝ) : ℝ :=
  -∫ θ in (0 : ℝ)..(Real.pi / 2),
    Real.cos θ ^ 2 * Real.cos (u * Real.cos θ) * Real.log (Real.sin θ)

theorem intervalIntegrable_abs_log_sin (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => |Real.log (Real.sin θ)|) volume a b := by
  have h : IntervalIntegrable (Real.log ∘ Real.sin) volume a b := intervalIntegrable_log_sin
  exact h.abs

theorem measurable_besselMIntegrand (u : ℝ) :
    Measurable fun θ : ℝ => Real.cos (u * Real.cos θ) * Real.log (Real.sin θ) := by
  fun_prop

theorem intervalIntegrable_besselMIntegrand (u a b : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => Real.cos (u * Real.cos θ) * Real.log (Real.sin θ)) volume a b := by
  have h : IntervalIntegrable (Real.log ∘ Real.sin) volume a b := intervalIntegrable_log_sin
  refine IntervalIntegrable.mono_fun h ((measurable_besselMIntegrand u).aestronglyMeasurable) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, Function.comp_apply]
  have h1 : |Real.cos (u * Real.cos θ)| ≤ 1 := Real.abs_cos_le_one _
  nlinarith [abs_nonneg (Real.log (Real.sin θ)), abs_nonneg (Real.cos (u * Real.cos θ))]

theorem hasDerivAt_besselM (u : ℝ) : HasDerivAt besselM (besselMDeriv u) u := by
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)
    (bound := fun θ : ℝ => |Real.log (Real.sin θ)|)
    (F := fun (x : ℝ) (θ : ℝ) => Real.cos (x * Real.cos θ) * Real.log (Real.sin θ))
    (F' := fun (x : ℝ) (θ : ℝ) =>
      -(Real.cos θ * Real.sin (x * Real.cos θ) * Real.log (Real.sin θ)))
    (x₀ := u) (s := Set.univ) (by simp)
    (Filter.Eventually.of_forall fun x =>
      ((measurable_besselMIntegrand x).aestronglyMeasurable).restrict)
    (intervalIntegrable_besselMIntegrand u _ _)
    (by
      refine ((Measurable.neg ?_).aestronglyMeasurable).restrict
      fun_prop)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      have h2 : |Real.sin (x * Real.cos θ)| ≤ 1 := Real.abs_sin_le_one _
      have hAB : |Real.cos θ| * |Real.sin (x * Real.cos θ)| ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (abs_nonneg (Real.sin (x * Real.cos θ)))]
      linarith [mul_le_mul_of_nonneg_right hAB (abs_nonneg (Real.log (Real.sin θ)))])
    (intervalIntegrable_abs_log_sin _ _)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      have hinner : HasDerivAt (fun y : ℝ => y * Real.cos θ) (Real.cos θ) x := by
        simpa using (hasDerivAt_id x).mul_const (Real.cos θ)
      have h := (Real.hasDerivAt_cos (x * Real.cos θ)).comp x hinner
      have h2 := h.mul_const (Real.log (Real.sin θ))
      have hval : -Real.sin (x * Real.cos θ) * Real.cos θ * Real.log (Real.sin θ)
          = -(Real.cos θ * Real.sin (x * Real.cos θ) * Real.log (Real.sin θ)) := by ring
      rw [hval] at h2
      exact h2)
  have hderiv := hmain.2
  have hval : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        -(Real.cos θ * Real.sin (u * Real.cos θ) * Real.log (Real.sin θ)))
      = besselMDeriv u := by
    rw [besselMDeriv, intervalIntegral.integral_neg]
  rw [hval] at hderiv
  exact hderiv

theorem measurable_besselMDerivIntegrand (u : ℝ) :
    Measurable fun θ : ℝ =>
      -(Real.cos θ * Real.sin (u * Real.cos θ) * Real.log (Real.sin θ)) := by
  fun_prop

theorem hasDerivAt_besselMDeriv (u : ℝ) : HasDerivAt besselMDeriv (besselMSecondDeriv u) u := by
  have hpres : besselMDeriv = fun x : ℝ => ∫ θ in (0 : ℝ)..(Real.pi / 2),
      -(Real.cos θ * Real.sin (x * Real.cos θ) * Real.log (Real.sin θ)) := by
    funext x
    rw [besselMDeriv, intervalIntegral.integral_neg]
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)
    (bound := fun θ : ℝ => |Real.log (Real.sin θ)|)
    (F := fun (x : ℝ) (θ : ℝ) => -(Real.cos θ * Real.sin (x * Real.cos θ) * Real.log (Real.sin θ)))
    (F' := fun (x : ℝ) (θ : ℝ) =>
      -(Real.cos θ ^ 2 * Real.cos (x * Real.cos θ) * Real.log (Real.sin θ)))
    (x₀ := u) (s := Set.univ) (by simp)
    (Filter.Eventually.of_forall fun x =>
      ((measurable_besselMDerivIntegrand x).aestronglyMeasurable).restrict)
    (by
      have h : IntervalIntegrable (Real.log ∘ Real.sin) volume 0 (Real.pi / 2) :=
        intervalIntegrable_log_sin
      refine IntervalIntegrable.mono_fun h
        ((measurable_besselMDerivIntegrand u).aestronglyMeasurable) ?_
      filter_upwards with θ
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, Function.comp_apply]
      have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      have h2 : |Real.sin (u * Real.cos θ)| ≤ 1 := Real.abs_sin_le_one _
      have hAB : |Real.cos θ| * |Real.sin (u * Real.cos θ)| ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (abs_nonneg (Real.sin (u * Real.cos θ)))]
      linarith [mul_le_mul_of_nonneg_right hAB (abs_nonneg (Real.log (Real.sin θ)))])
    (by
      refine ((Measurable.neg ?_).aestronglyMeasurable).restrict
      fun_prop)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : Real.cos θ ^ 2 ≤ 1 := by
        nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
      have h1' : |Real.cos θ ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg (Real.cos θ))]
        exact h1
      have h2 : |Real.cos (x * Real.cos θ)| ≤ 1 := Real.abs_cos_le_one _
      have hAB : |Real.cos θ ^ 2| * |Real.cos (x * Real.cos θ)| ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h1') (abs_nonneg (Real.cos (x * Real.cos θ)))]
      linarith [mul_le_mul_of_nonneg_right hAB (abs_nonneg (Real.log (Real.sin θ)))])
    (intervalIntegrable_abs_log_sin _ _)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      have hinner : HasDerivAt (fun y : ℝ => y * Real.cos θ) (Real.cos θ) x := by
        simpa using (hasDerivAt_id x).mul_const (Real.cos θ)
      have h := (Real.hasDerivAt_sin (x * Real.cos θ)).comp x hinner
      have h2 := (h.const_mul (Real.cos θ)).mul_const (Real.log (Real.sin θ))
      have h3 := h2.neg
      have hval : -(Real.cos θ * (Real.cos (x * Real.cos θ) * Real.cos θ)
            * Real.log (Real.sin θ))
          = -(Real.cos θ ^ 2 * Real.cos (x * Real.cos θ) * Real.log (Real.sin θ)) := by ring
      rw [hval] at h3
      exact h3)
  have hderiv := hmain.2
  have hval : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        -(Real.cos θ ^ 2 * Real.cos (u * Real.cos θ) * Real.log (Real.sin θ)))
      = besselMSecondDeriv u := by
    rw [besselMSecondDeriv, intervalIntegral.integral_neg]
  rw [hval] at hderiv
  rw [hpres]
  exact hderiv

/-! ## The integration by parts -/

private theorem intervalIntegrable_logSinMajorant (C a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => C * |Real.log (Real.sin θ)| + 1) volume a b :=
  ((intervalIntegrable_abs_log_sin a b).const_mul C).add intervalIntegrable_const

/-- A uniform integrability criterion for the log-weighted trigonometric integrands: any measurable
function dominated by `C |log (sin θ)| + 1` is interval integrable. -/
private theorem intervalIntegrable_of_le_logSin {f : ℝ → ℝ} {C a b : ℝ} (hC : 0 ≤ C)
    (hmeas : Measurable f) (hbd : ∀ θ : ℝ, |f θ| ≤ C * |Real.log (Real.sin θ)| + 1) :
    IntervalIntegrable f volume a b := by
  refine IntervalIntegrable.mono_fun (intervalIntegrable_logSinMajorant C a b)
    hmeas.aestronglyMeasurable ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * |Real.log (Real.sin θ)| + 1)]
  exact hbd θ

/-- The primitive of the integration by parts: `sin θ log (sin θ) · sin(u cos θ)`.  Its value at both
endpoints is zero — at `pi/2` because `log 1 = 0`, at `0` because `sin θ log (sin θ) → 0`. -/
def besselMPrimitive (u θ : ℝ) : ℝ :=
  Real.sin θ * Real.log (Real.sin θ) * Real.sin (u * Real.cos θ)

/-- Its derivative on the open interval. -/
def besselMPrimitiveDeriv (u θ : ℝ) : ℝ :=
  (Real.cos θ * Real.log (Real.sin θ) + Real.cos θ) * Real.sin (u * Real.cos θ)
    - u * Real.sin θ ^ 2 * Real.log (Real.sin θ) * Real.cos (u * Real.cos θ)

theorem continuous_besselMPrimitive (u : ℝ) : Continuous (besselMPrimitive u) := by
  have h1 : Continuous fun θ : ℝ => Real.sin θ * Real.log (Real.sin θ) :=
    Real.continuous_mul_log.comp Real.continuous_sin
  have h2 : Continuous fun θ : ℝ => Real.sin (u * Real.cos θ) := by fun_prop
  exact h1.mul h2

theorem hasDerivAt_besselMPrimitive {u θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    HasDerivAt (besselMPrimitive u) (besselMPrimitiveDeriv u θ) θ := by
  have hlog : HasDerivAt (fun t : ℝ => Real.log (Real.sin t))
      ((Real.sin θ)⁻¹ * Real.cos θ) θ := by
    have h := (Real.hasDerivAt_log hθ).comp θ (Real.hasDerivAt_sin θ)
    exact h
  have h1 : HasDerivAt (fun t : ℝ => Real.sin t * Real.log (Real.sin t))
      (Real.cos θ * Real.log (Real.sin θ) + Real.cos θ) θ := by
    have h := (Real.hasDerivAt_sin θ).fun_mul hlog
    have hval : Real.cos θ * Real.log (Real.sin θ)
          + Real.sin θ * ((Real.sin θ)⁻¹ * Real.cos θ)
        = Real.cos θ * Real.log (Real.sin θ) + Real.cos θ := by
      field_simp
    rw [hval] at h
    exact h
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (u * Real.cos t))
      (Real.cos (u * Real.cos θ) * (u * -Real.sin θ)) θ := by
    have hinner : HasDerivAt (fun t : ℝ => u * Real.cos t) (u * -Real.sin θ) θ :=
      (Real.hasDerivAt_cos θ).const_mul u
    exact (Real.hasDerivAt_sin (u * Real.cos θ)).comp θ hinner
  have h := h1.fun_mul h2
  have hval : (Real.cos θ * Real.log (Real.sin θ) + Real.cos θ) * Real.sin (u * Real.cos θ)
        + Real.sin θ * Real.log (Real.sin θ) * (Real.cos (u * Real.cos θ) * (u * -Real.sin θ))
      = besselMPrimitiveDeriv u θ := by
    rw [besselMPrimitiveDeriv]
    ring
  rw [hval] at h
  exact h

theorem measurable_besselMPrimitiveDeriv (u : ℝ) : Measurable (besselMPrimitiveDeriv u) := by
  unfold besselMPrimitiveDeriv
  fun_prop

theorem intervalIntegrable_besselMPrimitiveDeriv (u a b : ℝ) :
    IntervalIntegrable (besselMPrimitiveDeriv u) volume a b := by
  refine intervalIntegrable_of_le_logSin (C := 1 + |u|) (by positivity)
    (measurable_besselMPrimitiveDeriv u) fun θ => ?_
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hsu : |Real.sin (u * Real.cos θ)| ≤ 1 := Real.abs_sin_le_one _
  have hcu : |Real.cos (u * Real.cos θ)| ≤ 1 := Real.abs_cos_le_one _
  have hL : (0 : ℝ) ≤ |Real.log (Real.sin θ)| := abs_nonneg _
  have hterm1 : |(Real.cos θ * Real.log (Real.sin θ) + Real.cos θ) * Real.sin (u * Real.cos θ)|
      ≤ |Real.log (Real.sin θ)| + 1 := by
    have h1 : |(Real.cos θ * Real.log (Real.sin θ) + Real.cos θ) * Real.sin (u * Real.cos θ)|
        ≤ |Real.cos θ * Real.log (Real.sin θ) + Real.cos θ| := by
      rw [abs_mul]
      nlinarith [abs_nonneg (Real.cos θ * Real.log (Real.sin θ) + Real.cos θ), hsu]
    have h2 : |Real.cos θ * Real.log (Real.sin θ) + Real.cos θ|
        ≤ |Real.log (Real.sin θ)| + 1 := by
      calc |Real.cos θ * Real.log (Real.sin θ) + Real.cos θ|
          ≤ |Real.cos θ * Real.log (Real.sin θ)| + |Real.cos θ| := abs_add_le _ _
        _ ≤ |Real.log (Real.sin θ)| + 1 := by
            rw [abs_mul]
            nlinarith [hc, hL]
    linarith
  have hterm2 : |u * Real.sin θ ^ 2 * Real.log (Real.sin θ) * Real.cos (u * Real.cos θ)|
      ≤ |u| * |Real.log (Real.sin θ)| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
    have hssq : Real.sin θ ^ 2 ≤ 1 := by nlinarith [hs, abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
    have h1 : |u| * Real.sin θ ^ 2 ≤ |u| := by nlinarith [abs_nonneg u, sq_nonneg (Real.sin θ)]
    calc |u| * Real.sin θ ^ 2 * |Real.log (Real.sin θ)| * |Real.cos (u * Real.cos θ)|
        ≤ |u| * Real.sin θ ^ 2 * |Real.log (Real.sin θ)| * 1 := by
          have hpos : (0 : ℝ) ≤ |u| * Real.sin θ ^ 2 * |Real.log (Real.sin θ)| := by positivity
          nlinarith [hcu, hpos]
      _ ≤ |u| * |Real.log (Real.sin θ)| := by nlinarith [h1, hL]
  calc |besselMPrimitiveDeriv u θ|
      ≤ |(Real.cos θ * Real.log (Real.sin θ) + Real.cos θ) * Real.sin (u * Real.cos θ)|
        + |u * Real.sin θ ^ 2 * Real.log (Real.sin θ) * Real.cos (u * Real.cos θ)| := by
        rw [besselMPrimitiveDeriv]
        exact abs_sub _ _
    _ ≤ (|Real.log (Real.sin θ)| + 1) + |u| * |Real.log (Real.sin θ)| := by linarith
    _ = (1 + |u|) * |Real.log (Real.sin θ)| + 1 := by ring

/-- **The integration by parts.**  The primitive vanishes at both endpoints, so its derivative
integrates to zero over the quarter period. -/
theorem integral_besselMPrimitiveDeriv (u : ℝ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), besselMPrimitiveDeriv u θ) = 0 := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hcont : ContinuousOn (besselMPrimitive u) (Icc 0 (Real.pi / 2)) :=
    (continuous_besselMPrimitive u).continuousOn
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (besselMPrimitive u) (besselMPrimitiveDeriv u θ) (Ioi θ) θ := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by
      have := Real.pi_pos
      linarith [hθ.2])
    exact (hasDerivAt_besselMPrimitive hs.ne').hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hpi hcont hderiv
    (intervalIntegrable_besselMPrimitiveDeriv u _ _)
  rw [h, besselMPrimitive, besselMPrimitive]
  rw [Real.sin_pi_div_two, Real.log_one, Real.sin_zero, Real.log_zero]
  ring

/-! ## Bessel's equation for the second solution -/

private theorem integrable_trig_logSin {g : ℝ → ℝ} (a b : ℝ) (hmeas : Measurable g)
    (hbd : ∀ θ : ℝ, |g θ| ≤ |Real.log (Real.sin θ)|) :
    IntervalIntegrable g volume a b := by
  refine intervalIntegrable_of_le_logSin (C := 1) (by norm_num) hmeas fun θ => ?_
  have := hbd θ
  nlinarith [this]

private theorem intI1 (u a b : ℝ) : IntervalIntegrable
    (fun θ : ℝ => Real.cos θ * Real.log (Real.sin θ) * Real.sin (u * Real.cos θ)) volume a b := by
  refine integrable_trig_logSin a b (by fun_prop) fun θ => ?_
  rw [abs_mul, abs_mul]
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hsu : |Real.sin (u * Real.cos θ)| ≤ 1 := Real.abs_sin_le_one _
  have hL : (0 : ℝ) ≤ |Real.log (Real.sin θ)| := abs_nonneg _
  nlinarith [mul_nonneg (abs_nonneg (Real.cos θ)) hL, hc, hsu, abs_nonneg (Real.cos θ)]

private theorem intI3 (u a b : ℝ) : IntervalIntegrable
    (fun θ : ℝ => Real.sin θ ^ 2 * Real.log (Real.sin θ) * Real.cos (u * Real.cos θ))
    volume a b := by
  refine integrable_trig_logSin a b (by fun_prop) fun θ => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hs : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
  have hcu : |Real.cos (u * Real.cos θ)| ≤ 1 := Real.abs_cos_le_one _
  have hL : (0 : ℝ) ≤ |Real.log (Real.sin θ)| := abs_nonneg _
  nlinarith [mul_nonneg (sq_nonneg (Real.sin θ)) hL, hs, hcu]

private theorem intI4 (u a b : ℝ) : IntervalIntegrable
    (fun θ : ℝ => Real.cos θ ^ 2 * Real.cos (u * Real.cos θ) * Real.log (Real.sin θ))
    volume a b := by
  refine integrable_trig_logSin a b (by fun_prop) fun θ => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have hcu : |Real.cos (u * Real.cos θ)| ≤ 1 := Real.abs_cos_le_one _
  have hL : (0 : ℝ) ≤ |Real.log (Real.sin θ)| := abs_nonneg _
  have hAB : Real.cos θ ^ 2 * |Real.cos (u * Real.cos θ)| ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (abs_nonneg (Real.cos (u * Real.cos θ))),
      abs_nonneg (Real.cos (u * Real.cos θ)), sq_nonneg (Real.cos θ)]
  linarith [mul_le_mul_of_nonneg_right hAB hL]

private theorem intI6 (u a b : ℝ) : IntervalIntegrable
    (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos (u * Real.cos θ) * Real.log (Real.sin θ))
    volume a b := by
  refine integrable_trig_logSin a b (by fun_prop) fun θ => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hs : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
  have hcu : |Real.cos (u * Real.cos θ)| ≤ 1 := Real.abs_cos_le_one _
  have hL : (0 : ℝ) ≤ |Real.log (Real.sin θ)| := abs_nonneg _
  have hAB : Real.sin θ ^ 2 * |Real.cos (u * Real.cos θ)| ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg (Real.cos (u * Real.cos θ))),
      abs_nonneg (Real.cos (u * Real.cos θ)), sq_nonneg (Real.sin θ)]
  linarith [mul_le_mul_of_nonneg_right hAB hL]

private theorem intI7 (u a b : ℝ) : IntervalIntegrable
    (fun θ : ℝ => Real.cos θ * Real.sin (u * Real.cos θ) * Real.log (Real.sin θ))
    volume a b := by
  refine integrable_trig_logSin a b (by fun_prop) fun θ => ?_
  rw [abs_mul, abs_mul]
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hsu : |Real.sin (u * Real.cos θ)| ≤ 1 := Real.abs_sin_le_one _
  have hL : (0 : ℝ) ≤ |Real.log (Real.sin θ)| := abs_nonneg _
  have hAB : |Real.cos θ| * |Real.sin (u * Real.cos θ)| ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (abs_nonneg (Real.sin (u * Real.cos θ)))]
  linarith [mul_le_mul_of_nonneg_right hAB hL]

/-- The `sin²`-weighted form of `M'' + M`. -/
theorem besselMSecondDeriv_add_besselM (u : ℝ) :
    besselMSecondDeriv u + besselM u
      = ∫ θ in (0 : ℝ)..(Real.pi / 2),
          Real.sin θ ^ 2 * Real.cos (u * Real.cos θ) * Real.log (Real.sin θ) := by
  have key : (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.cos θ) * Real.log (Real.sin θ))
      - (∫ θ in (0 : ℝ)..(Real.pi / 2),
          Real.cos θ ^ 2 * Real.cos (u * Real.cos θ) * Real.log (Real.sin θ))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2),
          Real.sin θ ^ 2 * Real.cos (u * Real.cos θ) * Real.log (Real.sin θ) := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_besselMIntegrand u _ _)
      (intI4 u _ _)]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hpy : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hpy]
    ring
  rw [besselMSecondDeriv, besselM]
  linarith [key]

/-- **The defect identity.**  One integration by parts turns the log-weighted integral into the exact
inhomogeneous Bessel relation `u(M'' + M) + M' = -(pi/2) J_0'`. -/
theorem besselM_defect (u : ℝ) :
    u * (besselMSecondDeriv u + besselM u) + besselMDeriv u
      = -(Real.pi / 2) * besselJ0Deriv u := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  -- expand the integration by parts
  have hzero := integral_besselMPrimitiveDeriv u
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2), besselMPrimitiveDeriv u θ)
      = ((∫ θ in (0 : ℝ)..(Real.pi / 2),
            Real.cos θ * Real.log (Real.sin θ) * Real.sin (u * Real.cos θ))
          + ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ * Real.sin (u * Real.cos θ))
        - u * ∫ θ in (0 : ℝ)..(Real.pi / 2),
            Real.sin θ ^ 2 * Real.cos (u * Real.cos θ) * Real.log (Real.sin θ) := by
    have hcont : IntervalIntegrable
        (fun θ : ℝ => Real.cos θ * Real.sin (u * Real.cos θ)) volume 0 (Real.pi / 2) := by
      refine Continuous.intervalIntegrable ?_ _ _
      fun_prop
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (intI1 u _ _) hcont,
      ← intervalIntegral.integral_sub ((intI1 u _ _).add hcont)
        ((intI6 u _ _).const_mul u)]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [besselMPrimitiveDeriv]
    ring
  -- the two named pieces
  have hM' : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      Real.cos θ * Real.log (Real.sin θ) * Real.sin (u * Real.cos θ)) = -besselMDeriv u := by
    rw [besselMDeriv, neg_neg]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  have hJ : (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ * Real.sin (u * Real.cos θ))
      = -(Real.pi / 2) * besselJ0Deriv u := by
    rw [besselJ0Deriv_cos_form]
    generalize (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ * Real.sin (u * Real.cos θ)) = I
    field_simp
  rw [hsplit, hM', hJ, ← besselMSecondDeriv_add_besselM] at hzero
  linarith [hzero]

/-- The second solution of Bessel's equation of order zero, built from absolutely convergent data. -/
def besselK (u : ℝ) : ℝ := Real.pi / 4 * Real.log u * besselJ0 u + besselM u

/-- Its derivative. -/
def besselKDeriv (u : ℝ) : ℝ :=
  Real.pi / 4 * (besselJ0 u / u + Real.log u * besselJ0Deriv u) + besselMDeriv u

theorem hasDerivAt_besselK {u : ℝ} (hu : 0 < u) : HasDerivAt besselK (besselKDeriv u) u := by
  have hune : u ≠ 0 := hu.ne'
  have hlog : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hune
  have h1 : HasDerivAt (fun t : ℝ => Real.pi / 4 * Real.log t * besselJ0 t)
      (Real.pi / 4 * (besselJ0 u / u + Real.log u * besselJ0Deriv u)) u := by
    have h := ((hlog.const_mul (Real.pi / 4)).fun_mul (hasDerivAt_besselJ0 u))
    have hval : Real.pi / 4 * u⁻¹ * besselJ0 u
          + Real.pi / 4 * Real.log u * besselJ0Deriv u
        = Real.pi / 4 * (besselJ0 u / u + Real.log u * besselJ0Deriv u) := by
      field_simp
    rw [hval] at h
    exact h
  have h := h1.fun_add (hasDerivAt_besselM u)
  exact h

/-- The second derivative of the second solution. -/
def besselKSecondDeriv (u : ℝ) : ℝ :=
  Real.pi / 4 * (2 * besselJ0Deriv u / u - besselJ0 u / u ^ 2
      + Real.log u * besselJ0SecondDeriv u)
    + besselMSecondDeriv u

theorem hasDerivAt_besselKDeriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt besselKDeriv (besselKSecondDeriv u) u := by
  have hune : u ≠ 0 := hu.ne'
  have hlog : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hune
  have hquot : HasDerivAt (fun t : ℝ => besselJ0 t / t)
      ((besselJ0Deriv u * u - besselJ0 u * 1) / u ^ 2) u :=
    (hasDerivAt_besselJ0 u).fun_div (hasDerivAt_id u) hune
  have hprod : HasDerivAt (fun t : ℝ => Real.log t * besselJ0Deriv t)
      (u⁻¹ * besselJ0Deriv u + Real.log u * besselJ0SecondDeriv u) u :=
    hlog.fun_mul (hasDerivAt_besselJ0Deriv u)
  have hsum := (hquot.fun_add hprod).const_mul (Real.pi / 4)
  have h := hsum.fun_add (hasDerivAt_besselMDeriv u)
  have hval : Real.pi / 4 * ((besselJ0Deriv u * u - besselJ0 u * 1) / u ^ 2
        + (u⁻¹ * besselJ0Deriv u + Real.log u * besselJ0SecondDeriv u))
      + besselMSecondDeriv u
      = besselKSecondDeriv u := by
    rw [besselKSecondDeriv]
    field_simp
    ring
  rw [hval] at h
  exact h

/-- **Bessel's equation for the second solution**, in the division-free self-adjoint form
`u K'' + K' + u K = 0`.  The `log u` terms cancel through Bessel's equation for `J_0`, and the
inhomogeneous defect of the log-weighted integral cancels the `2 J_0'/u` produced by differentiating
`log u · J_0` twice. -/
theorem besselK_ode {u : ℝ} (hu : 0 < u) :
    u * besselKSecondDeriv u + besselKDeriv u + u * besselK u = 0 := by
  have hune : u ≠ 0 := hu.ne'
  have hode' : u * besselJ0SecondDeriv u + besselJ0Deriv u + u * besselJ0 u = 0 := by
    have h := besselJ0_ode hune
    field_simp at h
    linarith [h]
  have hdef := besselM_defect u
  have hLHS : u * besselKSecondDeriv u + besselKDeriv u + u * besselK u
      = Real.pi / 4 * (2 * besselJ0Deriv u
          + Real.log u * (u * besselJ0SecondDeriv u + besselJ0Deriv u + u * besselJ0 u))
        + (u * (besselMSecondDeriv u + besselM u) + besselMDeriv u) := by
    rw [besselKSecondDeriv, besselKDeriv, besselK]
    field_simp
    ring
  rw [hLHS, hode', hdef]
  ring

/-! ## Bounds on the log-weighted integral -/

theorem integral_abs_log_sin_quarter :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), |Real.log (Real.sin θ)|)
      = Real.pi / 2 * Real.log 2 := by
  have hcongr : (∫ θ in (0 : ℝ)..(Real.pi / 2), |Real.log (Real.sin θ)|)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), -Real.log (Real.sin θ) := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    have hs0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
    have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    exact abs_of_nonpos (Real.log_nonpos hs0 hs1)
  rw [hcongr, intervalIntegral.integral_neg, integral_log_sin_zero_pi_div_two]
  ring

theorem abs_besselM_le (u : ℝ) : |besselM u| ≤ Real.pi / 2 * Real.log 2 := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hnorm : ‖∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.cos (u * Real.cos θ) * Real.log (Real.sin θ)‖
      ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2),
          ‖Real.cos (u * Real.cos θ) * Real.log (Real.sin θ)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hpi
  have hmono : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        ‖Real.cos (u * Real.cos θ) * Real.log (Real.sin θ)‖)
      ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), |Real.log (Real.sin θ)| := by
    refine intervalIntegral.integral_mono_on hpi
      ((intervalIntegrable_besselMIntegrand u 0 (Real.pi / 2)).norm)
      (intervalIntegrable_abs_log_sin _ _) fun θ _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.cos (u * Real.cos θ)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [abs_nonneg (Real.log (Real.sin θ)), abs_nonneg (Real.cos (u * Real.cos θ))]
  rw [besselM, ← Real.norm_eq_abs]
  rw [integral_abs_log_sin_quarter] at hmono
  linarith

theorem abs_besselMDeriv_le (u : ℝ) : |besselMDeriv u| ≤ Real.pi / 2 * Real.log 2 := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hnorm : ‖∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.cos θ * Real.sin (u * Real.cos θ) * Real.log (Real.sin θ)‖
      ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2),
          ‖Real.cos θ * Real.sin (u * Real.cos θ) * Real.log (Real.sin θ)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hpi
  have hmono : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        ‖Real.cos θ * Real.sin (u * Real.cos θ) * Real.log (Real.sin θ)‖)
      ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), |Real.log (Real.sin θ)| := by
    refine intervalIntegral.integral_mono_on hpi ((intI7 u 0 (Real.pi / 2)).norm)
      (intervalIntegrable_abs_log_sin _ _) fun θ _ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have hsu : |Real.sin (u * Real.cos θ)| ≤ 1 := Real.abs_sin_le_one _
    have hL : (0 : ℝ) ≤ |Real.log (Real.sin θ)| := abs_nonneg _
    have hAB : |Real.cos θ| * |Real.sin (u * Real.cos θ)| ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (abs_nonneg (Real.sin (u * Real.cos θ)))]
    linarith [mul_le_mul_of_nonneg_right hAB hL]
  rw [besselMDeriv, abs_neg, ← Real.norm_eq_abs]
  rw [integral_abs_log_sin_quarter] at hmono
  linarith

/-! ## Elementary bounds on `J_0` and `J_0'` -/

theorem abs_besselJ0Deriv_le_one (u : ℝ) : |besselJ0Deriv u| ≤ 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbd : ‖∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)‖
      ≤ 1 * |Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have h2 : |Real.sin (u * Real.sin θ)| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.sin (u * Real.sin θ))]
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hpi, one_mul] at hbd
  rw [besselJ0Deriv, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi)]
  calc 1 / Real.pi * |∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ 1 / Real.pi * Real.pi := by
        exact mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = 1 := by field_simp

/-- A quadratic lower bound near the origin: `J_0(u) >= 1 - u²/2`. -/
theorem one_sub_sq_div_two_le_besselJ0 (u : ℝ) : 1 - u ^ 2 / 2 ≤ besselJ0 u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcont : Continuous fun θ : ℝ => Real.cos (u * Real.sin θ) := by fun_prop
  have hmono : (∫ θ in (0 : ℝ)..Real.pi, (1 - u ^ 2 / 2))
      ≤ ∫ θ in (0 : ℝ)..Real.pi, Real.cos (u * Real.sin θ) := by
    refine intervalIntegral.integral_mono_on hpi.le intervalIntegrable_const
      (hcont.intervalIntegrable _ _) fun θ hθ => ?_
    have hlow : 1 - (u * Real.sin θ) ^ 2 / 2 ≤ Real.cos (u * Real.sin θ) :=
      Real.one_sub_sq_div_two_le_cos
    have hs : Real.sin θ ^ 2 ≤ 1 := by
      nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
    nlinarith [hlow, hs, sq_nonneg u, sq_nonneg (Real.sin θ)]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  have h := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
  rw [show 1 / Real.pi * (Real.pi * (1 - u ^ 2 / 2)) = 1 - u ^ 2 / 2 from by field_simp] at h
  rw [besselJ0]
  exact h

/-! ## The weighted Wronskian is a nonzero constant -/

/-- The weighted Wronskian of the two solutions, `u (J_0 K' - J_0' K)`.  Abel's identity for the
self-adjoint form makes it constant. -/
def besselWronskian (u : ℝ) : ℝ :=
  u * (besselJ0 u * besselKDeriv u - besselJ0Deriv u * besselK u)

/-- The log terms cancel: the Wronskian is `(pi/4) J_0² plus a bounded remainder`. -/
theorem besselWronskian_eq {u : ℝ} (hu : 0 < u) :
    besselWronskian u = Real.pi / 4 * besselJ0 u ^ 2
      + u * (besselJ0 u * besselMDeriv u - besselJ0Deriv u * besselM u) := by
  have hune : u ≠ 0 := hu.ne'
  rw [besselWronskian, besselKDeriv, besselK]
  field_simp
  ring

theorem besselJ0_ode_cleared {u : ℝ} (hu : u ≠ 0) :
    u * besselJ0SecondDeriv u + besselJ0Deriv u + u * besselJ0 u = 0 := by
  have h := besselJ0_ode hu
  field_simp at h
  linarith [h]

/-- **Abel's identity.**  The weighted Wronskian has zero derivative. -/
theorem hasDerivAt_besselWronskian {u : ℝ} (hu : 0 < u) : HasDerivAt besselWronskian 0 u := by
  have hune : u ≠ 0 := hu.ne'
  have hJ := besselJ0_ode_cleared hune
  have hK := besselK_ode hu
  have h1 : HasDerivAt (fun t : ℝ => besselJ0 t * besselKDeriv t)
      (besselJ0Deriv u * besselKDeriv u + besselJ0 u * besselKSecondDeriv u) u :=
    (hasDerivAt_besselJ0 u).fun_mul (hasDerivAt_besselKDeriv hu)
  have h2 : HasDerivAt (fun t : ℝ => besselJ0Deriv t * besselK t)
      (besselJ0SecondDeriv u * besselK u + besselJ0Deriv u * besselKDeriv u) u :=
    (hasDerivAt_besselJ0Deriv u).fun_mul (hasDerivAt_besselK hu)
  have h3 := (hasDerivAt_id u).fun_mul (h1.fun_sub h2)
  simp only [id_eq] at h3
  have hval : 1 * (besselJ0 u * besselKDeriv u - besselJ0Deriv u * besselK u)
      + u * ((besselJ0Deriv u * besselKDeriv u + besselJ0 u * besselKSecondDeriv u)
        - (besselJ0SecondDeriv u * besselK u + besselJ0Deriv u * besselKDeriv u)) = 0 := by
    linear_combination (besselJ0 u) * hK - (besselK u) * hJ
  rw [hval] at h3
  exact h3

theorem besselWronskian_const {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    besselWronskian b = besselWronskian a := by
  have hpos : ∀ x ∈ Set.Icc a b, (0 : ℝ) < x := fun x hx => lt_of_lt_of_le ha hx.1
  have hcont : ContinuousOn besselWronskian (Set.Icc a b) := fun x hx =>
    ((hasDerivAt_besselWronskian (hpos x hx)).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt besselWronskian 0 (Set.Ici x) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    exact (hasDerivAt_besselWronskian hx0).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hderiv b ⟨hab, le_rfl⟩

/-- **The Wronskian is positive.**  Evaluated near the origin the `(pi/4) J_0²` term dominates the
bounded remainder: `J_0(1/10) >= 199/200` while both log-weighted integrals are at most
`(pi/2) log 2`. -/
theorem besselWronskian_pos {u : ℝ} (hu : 0 < u) : 0 < besselWronskian u := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : 0 < besselWronskian (1 / 10) := by
    have h10 : (0 : ℝ) < 1 / 10 := by norm_num
    rw [besselWronskian_eq h10]
    have hJlow : (199 : ℝ) / 200 ≤ besselJ0 (1 / 10) := by
      have h := one_sub_sq_div_two_le_besselJ0 (1 / 10)
      norm_num at h
      linarith [h]
    have hJup : besselJ0 (1 / 10) ≤ 1 := by
      have h := abs_besselJ0_le_one (1 / 10)
      exact (abs_le.mp h).2
    have hJsq : (199 : ℝ) / 200 * (199 / 200) ≤ besselJ0 (1 / 10) ^ 2 := by
      nlinarith [hJlow, hJup]
    have hMd := abs_besselMDeriv_le (1 / 10)
    have hM := abs_besselM_le (1 / 10)
    have hJd := abs_besselJ0Deriv_le_one (1 / 10)
    have hprod1 : |besselJ0 (1 / 10) * besselMDeriv (1 / 10)| ≤ Real.pi / 2 * Real.log 2 := by
      rw [abs_mul]
      have h1 : |besselJ0 (1 / 10)| ≤ 1 := abs_besselJ0_le_one _
      nlinarith [abs_nonneg (besselMDeriv (1 / 10)), abs_nonneg (besselJ0 (1 / 10)), hMd,
        mul_nonneg (abs_nonneg (besselJ0 (1 / 10))) (abs_nonneg (besselMDeriv (1 / 10)))]
    have hprod2 : |besselJ0Deriv (1 / 10) * besselM (1 / 10)| ≤ Real.pi / 2 * Real.log 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg (besselM (1 / 10)), abs_nonneg (besselJ0Deriv (1 / 10)), hM, hJd,
        mul_nonneg (abs_nonneg (besselJ0Deriv (1 / 10))) (abs_nonneg (besselM (1 / 10)))]
    have hrem : |besselJ0 (1 / 10) * besselMDeriv (1 / 10)
          - besselJ0Deriv (1 / 10) * besselM (1 / 10)|
        ≤ 2 * (Real.pi / 2 * Real.log 2) := by
      calc |besselJ0 (1 / 10) * besselMDeriv (1 / 10)
              - besselJ0Deriv (1 / 10) * besselM (1 / 10)|
          ≤ |besselJ0 (1 / 10) * besselMDeriv (1 / 10)|
            + |besselJ0Deriv (1 / 10) * besselM (1 / 10)| := abs_sub _ _
        _ ≤ 2 * (Real.pi / 2 * Real.log 2) := by linarith
    have hrem' : -(2 * (Real.pi / 2 * Real.log 2))
        ≤ besselJ0 (1 / 10) * besselMDeriv (1 / 10)
          - besselJ0Deriv (1 / 10) * besselM (1 / 10) := (abs_le.mp hrem).1
    nlinarith [hJsq, hrem', hpi3, hpi4, hlog, hlog0]
  rcases le_total u (1 / 10) with h | h
  · rw [besselWronskian_const hu h] at *
    exact hkey
  · rw [besselWronskian_const (by norm_num : (0 : ℝ) < 1 / 10) h]
    exact hkey

theorem besselWronskian_ne_zero {u : ℝ} (hu : 0 < u) : besselWronskian u ≠ 0 :=
  (besselWronskian_pos hu).ne'

/-! ## The envelope of the second solution -/

/-- **The perturbed-harmonic energy law.**  If `v'' = -(1 + 1/(4x²)) v` on the ray `x >= 1` then the
energy `v² + v'²` never exceeds `exp(1/2)` times its initial value.  The mechanism is exact: the
weighted energy `(v² + v'²) exp(1/(2x) - 1/2)` has derivative
`-2q E (v v' + v² + v'²) <= 0`, because `v v' + v² + v'² = (v + v'/2)² + (3/4) v'²`. -/
theorem sq_add_sq_le_of_perturbed_harmonic {v dv : ℝ → ℝ}
    (hv : ∀ x : ℝ, 1 ≤ x → HasDerivAt v (dv x) x)
    (hdv : ∀ x : ℝ, 1 ≤ x → HasDerivAt dv (-(1 + 1 / (4 * x ^ 2)) * v x) x)
    {x : ℝ} (hx : 1 ≤ x) :
    v x ^ 2 + dv x ^ 2 ≤ (v 1 ^ 2 + dv 1 ^ 2) * Real.exp (1 / 2) := by
  set E : ℝ → ℝ := fun t => Real.exp (1 / (2 * t) - 1 / 2) with hEdef
  set h : ℝ → ℝ := fun t => (v t ^ 2 + dv t ^ 2) * E t with hhdef
  have hEpos : ∀ t : ℝ, 0 < E t := fun t => Real.exp_pos _
  have hEderiv : ∀ t : ℝ, 0 < t → HasDerivAt E (-(1 / (2 * t ^ 2)) * E t) t := by
    intro t ht
    have hinner : HasDerivAt (fun s : ℝ => 1 / (2 * s) - 1 / 2) (-(1 / (2 * t ^ 2))) t := by
      have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
        simpa using (hasDerivAt_id t).const_mul 2
      have h2 := (hasDerivAt_const t (1 : ℝ)).fun_div h1 (by positivity)
      have hval : ((0 : ℝ) * (2 * t) - 1 * 2) / (2 * t) ^ 2 = -(1 / (2 * t ^ 2)) := by
        field_simp
        ring
      rw [hval] at h2
      exact (h2.sub_const (1 / 2))
    have h := hinner.exp
    rw [hEdef]
    exact h.congr_deriv (by ring)
  have hAderiv : ∀ t : ℝ, 1 ≤ t →
      HasDerivAt (fun s : ℝ => v s ^ 2 + dv s ^ 2)
        (-(2 * (1 / (4 * t ^ 2))) * (v t * dv t)) t := by
    intro t ht
    have hsq : (fun s : ℝ => v s ^ 2) = fun s : ℝ => v s * v s := by
      funext s
      ring
    have hsq' : (fun s : ℝ => dv s ^ 2) = fun s : ℝ => dv s * dv s := by
      funext s
      ring
    have h1 : HasDerivAt (fun s : ℝ => v s ^ 2) (2 * v t * dv t) t := by
      rw [hsq, show (2 * v t * dv t) = dv t * v t + v t * dv t from by ring]
      exact (hv t ht).fun_mul (hv t ht)
    have h2 : HasDerivAt (fun s : ℝ => dv s ^ 2)
        (2 * dv t * (-(1 + 1 / (4 * t ^ 2)) * v t)) t := by
      rw [hsq', show (2 * dv t * (-(1 + 1 / (4 * t ^ 2)) * v t))
        = (-(1 + 1 / (4 * t ^ 2)) * v t) * dv t + dv t * (-(1 + 1 / (4 * t ^ 2)) * v t) from by
          ring]
      exact (hdv t ht).fun_mul (hdv t ht)
    have h := h1.fun_add h2
    have hval : 2 * v t * dv t + 2 * dv t * (-(1 + 1 / (4 * t ^ 2)) * v t)
        = -(2 * (1 / (4 * t ^ 2))) * (v t * dv t) := by ring
    rw [hval] at h
    exact h
  have hhderiv : ∀ t : ℝ, 1 ≤ t → HasDerivAt h
      (-(2 * (1 / (4 * t ^ 2))) * E t * (v t * dv t + (v t ^ 2 + dv t ^ 2))) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have h := (hAderiv t ht).fun_mul (hEderiv t ht0)
    have hval : -(2 * (1 / (4 * t ^ 2))) * (v t * dv t) * E t
          + (v t ^ 2 + dv t ^ 2) * (-(1 / (2 * t ^ 2)) * E t)
        = -(2 * (1 / (4 * t ^ 2))) * E t * (v t * dv t + (v t ^ 2 + dv t ^ 2)) := by
      field_simp
      ring
    rw [hval] at h
    exact h
  -- the weighted energy is antitone
  have hanti : AntitoneOn h (Set.Ici 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1) ?_ ?_ ?_
    · intro t ht
      exact ((hhderiv t ht).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact ((hhderiv t (le_of_lt ht)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : (1 : ℝ) < t := ht
      rw [(hhderiv t ht1.le).deriv]
      have hq : (0 : ℝ) < 2 * (1 / (4 * t ^ 2)) := by positivity
      have hsum : 0 ≤ v t * dv t + (v t ^ 2 + dv t ^ 2) := by
        nlinarith [sq_nonneg (v t + dv t / 2), sq_nonneg (dv t)]
      have := mul_nonneg (mul_nonneg hq.le (hEpos t).le) hsum
      linarith [this]
  have hle := hanti (Set.self_mem_Ici) (by exact hx : x ∈ Set.Ici (1 : ℝ)) hx
  -- unwind the weight
  have hE1 : E 1 = 1 := by
    rw [hEdef]
    norm_num
  have hEx : Real.exp (-(1 / 2)) ≤ E x := by
    rw [hEdef]
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) < 1 / (2 * x) := by positivity
    linarith
  have hAnn : 0 ≤ v x ^ 2 + dv x ^ 2 := by positivity
  have hA1nn : 0 ≤ v 1 ^ 2 + dv 1 ^ 2 := by positivity
  rw [hhdef] at hle
  simp only at hle
  rw [hE1, mul_one] at hle
  -- (A x) * E x ≤ A 1
  have hstep : (v x ^ 2 + dv x ^ 2) * Real.exp (-(1 / 2)) ≤ v 1 ^ 2 + dv 1 ^ 2 := by
    calc (v x ^ 2 + dv x ^ 2) * Real.exp (-(1 / 2))
        ≤ (v x ^ 2 + dv x ^ 2) * E x := by
          exact mul_le_mul_of_nonneg_left hEx hAnn
      _ ≤ v 1 ^ 2 + dv 1 ^ 2 := hle
  have hexp : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [hstep, Real.exp_pos (-(1 / 2)), Real.exp_pos (1 / 2 : ℝ), hexp, hAnn]

/-! ### The energy law applied to the second solution -/

/-- The Liouville–Green normalisation of the second solution. -/
def besselKV (x : ℝ) : ℝ := Real.sqrt x * besselK x

/-- Its derivative. -/
def besselKVDeriv (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt x) * besselK x + Real.sqrt x * besselKDeriv x

theorem hasDerivAt_besselKV {x : ℝ} (hx : 0 < x) : HasDerivAt besselKV (besselKVDeriv x) x :=
  (Real.hasDerivAt_sqrt hx.ne').mul (hasDerivAt_besselK hx)

theorem hasDerivAt_besselKVDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt besselKVDeriv (-(1 + 1 / (4 * x ^ 2)) * besselKV x) x := by
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx.ne'
  have hden : HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (2 * (1 / (2 * Real.sqrt x))) x :=
    hsqrt.const_mul 2
  have hinv : HasDerivAt (fun t : ℝ => 1 / (2 * Real.sqrt t))
      (-(1 / (4 * x * Real.sqrt x))) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).fun_div hden (by positivity)
    have h4 : (2 * Real.sqrt x) ^ 2 = 4 * x := by
      rw [mul_pow, Real.sq_sqrt hx.le]
      ring
    have hval : ((0 : ℝ) * (2 * Real.sqrt x) - 1 * (2 * (1 / (2 * Real.sqrt x))))
          / (2 * Real.sqrt x) ^ 2
        = -(1 / (4 * x * Real.sqrt x)) := by
      rw [h4]
      field_simp
      ring
    rw [hval] at h
    exact h
  have hprod1 : HasDerivAt (fun t : ℝ => 1 / (2 * Real.sqrt t) * besselK t)
      (-(1 / (4 * x * Real.sqrt x)) * besselK x
        + 1 / (2 * Real.sqrt x) * besselKDeriv x) x :=
    hinv.fun_mul (hasDerivAt_besselK hx)
  have hprod2 : HasDerivAt (fun t : ℝ => Real.sqrt t * besselKDeriv t)
      (1 / (2 * Real.sqrt x) * besselKDeriv x + Real.sqrt x * besselKSecondDeriv x) x :=
    hsqrt.fun_mul (hasDerivAt_besselKDeriv hx)
  have h := hprod1.fun_add hprod2
  have hode := besselK_ode hx
  have hval : -(1 / (4 * x * Real.sqrt x)) * besselK x
        + 1 / (2 * Real.sqrt x) * besselKDeriv x
      + (1 / (2 * Real.sqrt x) * besselKDeriv x + Real.sqrt x * besselKSecondDeriv x)
      = -(1 + 1 / (4 * x ^ 2)) * besselKV x := by
    obtain ⟨S, hS0, hSx, hSeq⟩ : ∃ S : ℝ, 0 < S ∧ S * S = x ∧ Real.sqrt x = S :=
      ⟨Real.sqrt x, hsx, hsq, rfl⟩
    have hode' : besselKSecondDeriv x = (-besselKDeriv x - x * besselK x) / x := by
      field_simp
      linarith [hode]
    rw [hode', besselKV, hSeq, ← hSx]
    field_simp
    ring
  rw [hval] at h
  exact h

/-- **The envelope of the second solution.**  `|K(u)| <= C u^{-1/2}` for `u >= 1`, with
`C = sqrt((K_V(1)² + K_V'(1)²) exp(1/2))`.  No asymptotic information about `K` is used: the energy law
does all the work, and this is what makes `K` an admissible partner of `J_0` in the Green kernel. -/
theorem exists_besselK_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 1 ≤ u → |besselK u| ≤ C / Real.sqrt u := by
  refine ⟨Real.sqrt ((besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2) * Real.exp (1 / 2)),
    Real.sqrt_nonneg _, fun u hu => ?_⟩
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  have henergy := sq_add_sq_le_of_perturbed_harmonic
    (v := besselKV) (dv := besselKVDeriv)
    (fun x hx => hasDerivAt_besselKV (lt_of_lt_of_le zero_lt_one hx))
    (fun x hx => hasDerivAt_besselKVDeriv (lt_of_lt_of_le zero_lt_one hx)) hu
  have hVsq : besselKV u ^ 2
      ≤ (besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2) * Real.exp (1 / 2) := by
    nlinarith [sq_nonneg (besselKVDeriv u), henergy]
  have hV : |besselKV u|
      ≤ Real.sqrt ((besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2) * Real.exp (1 / 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hVsq
  have hKV : |besselKV u| = Real.sqrt u * |besselK u| := by
    rw [besselKV, abs_mul, abs_of_nonneg (Real.sqrt_nonneg u)]
  rw [hKV] at hV
  rw [le_div_iff₀ hsu, mul_comm]
  exact hV

end GaloisForLFunctions.RHTower

end
