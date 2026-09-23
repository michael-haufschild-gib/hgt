import GaloisForLFunctions.HTGeometry.SteinhausIntervalBridge
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The sharp large-argument asymptotic of the circle Laplace transform

The corpus owns two envelopes for `I₀` with non-matching constants.  The card's `(27)` needs the
exact leading behaviour, and this module supplies it by Laplace's method:

`√x · e^{−x} · I₀(x) → 1/√(2π)`,   equivalently   `log I₀(x) − x + ½ log(2πx) → 0`.

The mechanism is the exact half-angle identity `cos y − 1 = −2 sin²(y/2)` together with the
rescaling `t = u/√x`: on the symmetric period `[−π, π]` the integrand becomes
`exp(x(cos(u/√x) − 1))`, which converges pointwise to the Gaussian `exp(−u²/2)` and is dominated by
`exp(−2u²/π²)` through Jordan's inequality.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

noncomputable section

/-- The exact half-angle identity behind the Gaussian limit. -/
theorem cos_sub_one_eq (y : ℝ) : Real.cos y - 1 = -(2 * Real.sin (y / 2) ^ (2 : ℕ)) := by
  have h := Real.sin_sq_eq_half_sub (y / 2)
  rw [show 2 * (y / 2) = y by ring] at h
  linarith

/-- Jordan's inequality in the form the domination needs. -/
theorem cos_sub_one_le {y : ℝ} (hy : |y| ≤ Real.pi) :
    Real.cos y - 1 ≤ -(2 * y ^ (2 : ℕ) / Real.pi ^ (2 : ℕ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey : ∀ z : ℝ, 0 ≤ z → z ≤ Real.pi →
      z ^ (2 : ℕ) ≤ Real.pi ^ (2 : ℕ) * Real.sin (z / 2) ^ (2 : ℕ) := by
    intro z hz0 hzpi
    have h1 : (0 : ℝ) ≤ z / 2 := by linarith
    have h2 : z / 2 ≤ Real.pi / 2 := by linarith
    have hj := Real.mul_le_sin h1 h2
    have hj' : z / Real.pi ≤ Real.sin (z / 2) := by
      have hid : 2 / Real.pi * (z / 2) = z / Real.pi := by field_simp
      rwa [hid] at hj
    have hzs : z ≤ Real.pi * Real.sin (z / 2) := by
      rw [div_le_iff₀ hpi] at hj'
      linarith
    have hsq : z ^ (2 : ℕ) ≤ (Real.pi * Real.sin (z / 2)) ^ (2 : ℕ) := pow_le_pow_left₀ hz0 hzs 2
    nlinarith [hsq]
  have habs := hkey |y| (abs_nonneg y) hy
  rw [sq_abs] at habs
  have hcos : Real.cos y = Real.cos |y| := (Real.cos_abs y).symm
  rw [hcos, cos_sub_one_eq]
  rw [neg_le_neg_iff, div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ (2 : ℕ))]
  nlinarith [habs]


/-- `sin y / y → 1` at the origin. -/
theorem tendsto_sin_div_nhdsNE :
    Tendsto (fun y : ℝ => Real.sin y / y) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h : HasDerivAt Real.sin (Real.cos 0) 0 := Real.hasDerivAt_sin 0
  rw [Real.cos_zero] at h
  have hslope := hasDerivAt_iff_tendsto_slope.1 h
  refine hslope.congr fun y => ?_
  rw [slope_def_field]
  simp

/-- The rescaled period integrand of the Bessel integral. -/
def gaussKernelSteinhaus (x u : ℝ) : ℝ := Real.exp (x * (Real.cos (u / Real.sqrt x) - 1))

/-- The rescaled period. -/
def gaussWindow (x : ℝ) : Set ℝ :=
  Ioc (-(Real.pi * Real.sqrt x)) (Real.pi * Real.sqrt x)

/-- The rescaled period integrand, extended by zero. -/
def gaussIndicator (x : ℝ) : ℝ → ℝ := (gaussWindow x).indicator (gaussKernelSteinhaus x)

theorem continuous_gaussKernelSteinhaus (x : ℝ) : Continuous (gaussKernelSteinhaus x) := by
  unfold gaussKernelSteinhaus
  exact Real.continuous_exp.comp
    (continuous_const.mul ((Real.continuous_cos.comp (continuous_id.div_const _)).sub
      continuous_const))

theorem gaussKernelSteinhaus_nonneg (x u : ℝ) : 0 ≤ gaussKernelSteinhaus x u := (Real.exp_pos _).le

theorem gaussIndicator_nonneg (x u : ℝ) : 0 ≤ gaussIndicator x u := by
  unfold gaussIndicator
  exact Set.indicator_nonneg (fun u _ => gaussKernelSteinhaus_nonneg x u) u

/-- The half-angle form of the rescaled integrand. -/
theorem gaussKernelSteinhaus_eq {x : ℝ} (hx : 0 ≤ x) (u : ℝ) :
    gaussKernelSteinhaus x u
      = Real.exp (-(2 * (Real.sqrt x * Real.sin (u / (2 * Real.sqrt x))) ^ (2 : ℕ))) := by
  have hsq : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx
  unfold gaussKernelSteinhaus
  congr 1
  rw [cos_sub_one_eq]
  have harg : u / Real.sqrt x / 2 = u / (2 * Real.sqrt x) := by ring
  rw [harg]
  nlinarith [hsq]

/-- The pointwise Gaussian limit. -/
theorem tendsto_gaussKernelSteinhaus {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun x : ℝ => gaussKernelSteinhaus x u) atTop (𝓝 (Real.exp (-(u ^ (2 : ℕ) / 2)))) := by
  have hsqrt : Tendsto Real.sqrt atTop atTop := Real.tendsto_sqrt_atTop
  have hy : Tendsto (fun x : ℝ => u / (2 * Real.sqrt x)) atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hden : Tendsto (fun x : ℝ => 2 * Real.sqrt x) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) hsqrt
      exact hden.const_div_atTop _
    · filter_upwards [hsqrt.eventually_gt_atTop 0] with x hx
      simp only [mem_compl_iff, mem_singleton_iff]
      exact div_ne_zero hu (by positivity)
  have hratio := tendsto_sin_div_nhdsNE.comp hy
  have hmul := hratio.const_mul (u / 2)
  rw [mul_one] at hmul
  have hlim : Tendsto (fun x : ℝ => Real.sqrt x * Real.sin (u / (2 * Real.sqrt x)))
      atTop (𝓝 (u / 2)) := by
    refine Tendsto.congr' ?_ hmul
    filter_upwards [hsqrt.eventually_gt_atTop 0] with x hx
    have hy0 : u / (2 * Real.sqrt x) ≠ 0 := div_ne_zero hu (by positivity)
    rw [Function.comp_apply]
    field_simp
  have hcomp : Tendsto (fun x : ℝ =>
      Real.exp (-(2 * (Real.sqrt x * Real.sin (u / (2 * Real.sqrt x))) ^ (2 : ℕ))))
      atTop (𝓝 (Real.exp (-(2 * (u / 2) ^ (2 : ℕ))))) :=
    (Real.continuous_exp.tendsto _).comp (((hlim.pow 2).const_mul 2).neg)
  rw [show -(2 * (u / 2) ^ (2 : ℕ)) = -(u ^ (2 : ℕ) / 2) by ring] at hcomp
  refine Tendsto.congr' ?_ hcomp
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (gaussKernelSteinhaus_eq hx u).symm


/-- The Gaussian domination. -/
theorem gaussIndicator_le {x : ℝ} (hx : 0 < x) (u : ℝ) :
    gaussIndicator x u ≤ Real.exp (-(2 / Real.pi ^ (2 : ℕ)) * u ^ (2 : ℕ)) := by
  unfold gaussIndicator
  by_cases hu : u ∈ gaussWindow x
  · rw [Set.indicator_of_mem hu]
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have hsq : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
    have hmem : u ∈ Ioc (-(Real.pi * Real.sqrt x)) (Real.pi * Real.sqrt x) := hu
    have habs : |u / Real.sqrt x| ≤ Real.pi := by
      rw [abs_div, abs_of_pos hsx, div_le_iff₀ hsx]
      rw [abs_le]
      constructor
      · nlinarith [hmem.1]
      · nlinarith [hmem.2]
    have hc := cos_sub_one_le habs
    have hy : (u / Real.sqrt x) ^ (2 : ℕ) = u ^ (2 : ℕ) / x := by
      rw [div_pow, hsq]
    rw [hy] at hc
    refine Real.exp_le_exp.2 ?_
    have hstep : x * (Real.cos (u / Real.sqrt x) - 1)
        ≤ x * (-(2 * (u ^ (2 : ℕ) / x) / Real.pi ^ (2 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left hc hx.le
    have hid : x * (-(2 * (u ^ (2 : ℕ) / x) / Real.pi ^ (2 : ℕ))) = -(2 / Real.pi ^ (2 : ℕ)) * u ^ (2 : ℕ) := by
      field_simp
    linarith [hstep, hid.le, hid.ge]
  · rw [Set.indicator_of_notMem hu]
    exact (Real.exp_pos _).le

/-- The Gaussian value of the limit integral. -/
theorem integral_exp_neg_half_sq : (∫ u : ℝ, Real.exp (-(u ^ (2 : ℕ) / 2))) = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with u
  congr 1
  ring

/-- **The Gaussian limit of the rescaled period integral.** -/
theorem tendsto_integral_gaussIndicator :
    Tendsto (fun x : ℝ => ∫ u, gaussIndicator x u) atTop (𝓝 (Real.sqrt (2 * Real.pi))) := by
  have hbound : Integrable (fun u : ℝ => Real.exp (-(2 / Real.pi ^ (2 : ℕ)) * u ^ (2 : ℕ))) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hmeas : ∀ᶠ x in atTop, AEStronglyMeasurable (gaussIndicator x) volume := by
    filter_upwards with x
    exact ((continuous_gaussKernelSteinhaus x).aestronglyMeasurable).indicator measurableSet_Ioc
  have hdom : ∀ᶠ x in atTop, ∀ᵐ u : ℝ,
      ‖gaussIndicator x u‖ ≤ Real.exp (-(2 / Real.pi ^ (2 : ℕ)) * u ^ (2 : ℕ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussIndicator_nonneg x u)]
    exact gaussIndicator_le hx u
  have hptw : ∀ᵐ u : ℝ,
      Tendsto (fun x : ℝ => gaussIndicator x u) atTop (𝓝 (Real.exp (-(u ^ (2 : ℕ) / 2)))) := by
    have hnull : (volume ({(0 : ℝ)} : Set ℝ)) = 0 := by simp
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hnull] with u hu
    have hu0 : u ≠ 0 := by
      simpa using hu
    have hker := tendsto_gaussKernelSteinhaus hu0
    refine Tendsto.congr' ?_ hker
    have hev : ∀ᶠ x : ℝ in atTop, |u| < Real.pi * Real.sqrt x := by
      have hsq : Tendsto (fun x : ℝ => Real.pi * Real.sqrt x) atTop atTop :=
        Filter.Tendsto.const_mul_atTop Real.pi_pos Real.tendsto_sqrt_atTop
      exact hsq.eventually_gt_atTop _
    filter_upwards [hev] with x hx
    have hmem : u ∈ gaussWindow x := by
      rw [abs_lt] at hx
      exact ⟨by linarith [hx.1], le_of_lt hx.2⟩
    rw [gaussIndicator, Set.indicator_of_mem hmem]
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (-(2 / Real.pi ^ (2 : ℕ)) * u ^ (2 : ℕ))) hmeas hdom hbound hptw
  rwa [integral_exp_neg_half_sq] at hdct


/-- The rescaled period integral IS the Bessel integral. -/
theorem integral_gaussIndicator_eq {x : ℝ} (hx : 0 < x) :
    (∫ u, gaussIndicator x u)
      = 2 * Real.pi * (Real.sqrt x * Real.exp (-x) * steinhausLaplace x) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle : -(Real.pi * Real.sqrt x) ≤ Real.pi * Real.sqrt x := by nlinarith
  have h1 : (∫ u, gaussIndicator x u)
      = ∫ u in (-(Real.pi * Real.sqrt x))..(Real.pi * Real.sqrt x), gaussKernelSteinhaus x u := by
    rw [gaussIndicator, gaussWindow, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le hle]
  have hsub := intervalIntegral.smul_integral_comp_mul_left (gaussKernelSteinhaus x) (Real.sqrt x)
    (a := -Real.pi) (b := Real.pi)
  have hends : Real.sqrt x * -Real.pi = -(Real.pi * Real.sqrt x) := by ring
  have hends' : Real.sqrt x * Real.pi = Real.pi * Real.sqrt x := by ring
  rw [hends, hends'] at hsub
  have h2 : (∫ t in (-Real.pi)..Real.pi, gaussKernelSteinhaus x (Real.sqrt x * t))
      = ∫ t in (-Real.pi)..Real.pi, Real.exp (-x) * Real.exp (x * Real.cos t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have harg : Real.sqrt x * t / Real.sqrt x = t := by field_simp
    simp only [gaussKernelSteinhaus, harg]
    rw [← Real.exp_add]
    congr 1
    ring
  have hper : Function.Periodic (fun t => Real.exp (x * Real.cos t)) (2 * Real.pi) := by
    intro t
    simp only []
    rw [Real.cos_periodic t]
  have h3 : (∫ t in (-Real.pi)..Real.pi, Real.exp (x * Real.cos t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (x * Real.cos t) := by
    have h := hper.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h
    exact h
  have h4 : (∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (x * Real.cos t))
      = 2 * Real.pi * steinhausLaplace x := by
    rw [steinhausLaplace_eq_intervalIntegral]
    field_simp
  rw [h1, ← hsub, h2, intervalIntegral.integral_const_mul, h3, h4, smul_eq_mul]
  ring

/-- **The sharp large-argument asymptotic:** `√x · e^{−x} · I₀(x) → 1/√(2π)`. -/
theorem tendsto_sqrt_mul_exp_neg_mul_steinhausLaplace :
    Tendsto (fun x : ℝ => Real.sqrt x * Real.exp (-x) * steinhausLaplace x) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi))) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hs : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 hpi
  have hdiv := tendsto_integral_gaussIndicator.div_const (2 * Real.pi)
  have hval : Real.sqrt (2 * Real.pi) / (2 * Real.pi) = 1 / Real.sqrt (2 * Real.pi) := by
    rw [div_eq_div_iff hpi.ne' hs.ne', Real.mul_self_sqrt hpi.le, one_mul]
  rw [hval] at hdiv
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [integral_gaussIndicator_eq hx]
  field_simp

/-- **The card's `(27)` in exact form:** `log I₀(x) − x + ½ log(2πx) → 0`. -/
theorem tendsto_steinhausLogLaplace_sub_sharp :
    Tendsto (fun x : ℝ =>
        steinhausLogLaplace x - x + (1 / 2) * Real.log (2 * Real.pi * x)) atTop (𝓝 0) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hs : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 hpi
  have hlim := tendsto_sqrt_mul_exp_neg_mul_steinhausLaplace
  have hpos : (0 : ℝ) < 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hlog := (Real.continuousAt_log hpos.ne').tendsto.comp hlim
  have hval : Real.log (1 / Real.sqrt (2 * Real.pi)) = -((1 / 2) * Real.log (2 * Real.pi)) := by
    rw [one_div, Real.log_inv, Real.log_sqrt hpi.le]
    ring
  rw [hval] at hlog
  have hshift := hlog.add_const ((1 / 2) * Real.log (2 * Real.pi))
  rw [neg_add_cancel] at hshift
  refine Tendsto.congr' ?_ hshift
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hI : 0 < steinhausLaplace x := steinhausLaplace_pos x
  rw [Function.comp_apply]
  rw [Real.log_mul (by positivity) hI.ne', Real.log_mul hsx.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_sqrt hx.le, Real.log_mul hpi.ne' hx.ne', steinhausLogLaplace]
  ring

end

end HTGeometry
