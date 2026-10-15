import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Logarithmic sine quantile profiles

The explicit profile `h_delta(t) = sin(pi t) * (1 + delta * log(1 + 1 / sin(pi t)))`
on `(0,1)` has a continuous zero-endpoint extension and is strictly concave for every
nonnegative `delta`. The two endpoint inequalities expose the `t log(1/t)` scale for
positive `delta`, while the scalar lift retains its exact derivative and curvature.

This is the source-calculus component of GTA's test of positive conductance Hankel
forms as a proposed control on nonnormal parity coupling. This file does not assert
a conductance moment representation, an entire-transform theorem, or a nonreal zero.
Those further statements require their own proofs.
-/

open Set Filter Topology
namespace RHTower
noncomputable section

/-- Continuous scalar lift underlying the logarithmic sine profile. -/
def logSineLift (δ x : ℝ) : ℝ :=
  x + δ * (x * Real.log (1 + x) - x * Real.log x)

def logSineLiftSlope (δ x : ℝ) : ℝ :=
  1 + δ * (Real.log (1 + x) - Real.log x - 1 / (1 + x))

def logSineProfile (δ t : ℝ) : ℝ := logSineLift δ (Real.sin (Real.pi * t))

def logSineProfileSlope (δ t : ℝ) : ℝ :=
  logSineLiftSlope δ (Real.sin (Real.pi * t)) * (Real.pi * Real.cos (Real.pi * t))

theorem logSineLift_eq {δ x : ℝ} (hx : 0 < x) :
    logSineLift δ x = x * (1 + δ * Real.log (1 + 1 / x)) := by
  have he : 1 + 1 / x = (1 + x) / x := by field_simp; ring
  rw [he, Real.log_div (by positivity) hx.ne']
  unfold logSineLift
  ring

theorem continuousAt_logSineLift {δ x : ℝ} (hx : 0 ≤ x) :
    ContinuousAt (logSineLift δ) x := by
  have hp : ContinuousAt (fun y : ℝ => Real.log (1 + y)) x :=
    (continuousAt_const.add continuousAt_id).log (show (1 : ℝ) + x ≠ 0 by linarith)
  exact continuousAt_id.add (continuousAt_const.mul
    ((continuousAt_id.mul hp).sub Real.continuous_mul_log.continuousAt))

theorem logSineLift_zero (δ : ℝ) : logSineLift δ 0 = 0 := by
  simp [logSineLift]

theorem logSineLift_ge {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) :
    x ≤ logSineLift δ x := by
  rw [logSineLift_eq hx]
  have hl : 0 ≤ Real.log (1 + 1 / x) := Real.log_nonneg (by have := one_div_pos.mpr hx; linarith)
  nlinarith [mul_nonneg hδ hl]

theorem logSineLiftSlope_ge_one {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) :
    1 ≤ logSineLiftSlope δ x := by
  have hbase := Real.one_sub_inv_le_log_of_pos (show 0 < (1 + x) / x by positivity)
  rw [Real.log_div (by positivity) hx.ne'] at hbase
  have he : 1 - ((1 + x) / x)⁻¹ = 1 / (1 + x) := by field_simp; ring
  rw [he] at hbase
  unfold logSineLiftSlope
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hbase)]

theorem hasDerivAt_logSineLift {δ x : ℝ} (hx : 0 < x) :
    HasDerivAt (logSineLift δ) (logSineLiftSlope δ x) x := by
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    simpa using ((hasDerivAt_id x).const_add 1).log (show 1 + x ≠ 0 by positivity)
  have h := (hasDerivAt_id x).add
    (((hasDerivAt_id x).mul hlog).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')) |>.const_mul δ)
  convert h using 1 <;> first | rfl | (dsimp [logSineLiftSlope]; field_simp [hx.ne', show 1 + x ≠ 0 by positivity]; ring)

theorem hasDerivAt_logSineLiftSlope {δ x : ℝ} (hx : 0 < x) :
    HasDerivAt (logSineLiftSlope δ) (-δ / (x * (1 + x) ^ 2)) x := by
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    simpa using ((hasDerivAt_id x).const_add 1).log (show 1 + x ≠ 0 by positivity)
  have hi : HasDerivAt (fun y : ℝ => 1 / (1 + y)) (-(1 / (1 + x) ^ 2)) x := by
    convert ((hasDerivAt_id x).const_add 1).inv
      (show 1 + x ≠ 0 by positivity) using 1 <;> first | rfl | (simp [one_div, neg_div, Pi.inv_def])
  have h := (((hlog.sub (Real.hasDerivAt_log hx.ne')).sub hi).const_mul δ).const_add 1
  convert h using 1 <;> first | rfl | (field_simp [hx.ne', show 1 + x ≠ 0 by positivity]; ring)

theorem logSineProfile_sine_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < Real.sin (Real.pi * t) := by
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
  simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 Real.pi_pos

theorem logSineProfile_pos {δ t : ℝ} (hδ : 0 ≤ δ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < logSineProfile δ t :=
  lt_of_lt_of_le (logSineProfile_sine_pos ht)
    (logSineLift_ge hδ (logSineProfile_sine_pos ht))

theorem logSineProfile_one_sub (δ t : ℝ) :
    logSineProfile δ (1 - t) = logSineProfile δ t := by
  unfold logSineProfile
  rw [mul_sub, mul_one, Real.sin_pi_sub]

theorem logSineProfile_zero (δ : ℝ) : logSineProfile δ 0 = 0 := by
  simp [logSineProfile, logSineLift_zero]

theorem logSineProfile_one (δ : ℝ) : logSineProfile δ 1 = 0 := by
  simp [logSineProfile, logSineLift_zero]

theorem continuousOn_logSineProfile (δ : ℝ) :
    ContinuousOn (logSineProfile δ) (Icc 0 1) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hs : ContinuousAt (fun s : ℝ => Real.sin (Real.pi * s)) t := by fun_prop
  exact ContinuousAt.comp (f := fun s : ℝ => Real.sin (Real.pi * s)) (g := logSineLift δ)
    (continuousAt_logSineLift (δ := δ) (Real.sin_nonneg_of_mem_Icc
      ⟨mul_nonneg Real.pi_pos.le ht.1, by nlinarith [Real.pi_pos, ht.2]⟩)) hs

theorem hasDerivAt_logSineProfile {δ t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (logSineProfile δ) (logSineProfileSlope δ t) t := by
  have hs := ((hasDerivAt_id t).const_mul Real.pi).sin
  convert (hasDerivAt_logSineLift (δ := δ) (logSineProfile_sine_pos ht)).comp t hs using 1
  all_goals first | rfl | (simp [logSineProfileSlope, mul_comm])

theorem hasDerivAt_logSineProfileSlope {δ t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (logSineProfileSlope δ)
      ((-δ / (Real.sin (Real.pi * t) * (1 + Real.sin (Real.pi * t)) ^ 2)) *
          (Real.pi * Real.cos (Real.pi * t)) ^ 2 -
        logSineLiftSlope δ (Real.sin (Real.pi * t)) * Real.pi ^ 2 *
          Real.sin (Real.pi * t)) t := by
  have hs := ((hasDerivAt_id t).const_mul Real.pi).sin
  have hc := (((hasDerivAt_id t).const_mul Real.pi).cos).const_mul Real.pi
  convert ((hasDerivAt_logSineLiftSlope (δ := δ) (logSineProfile_sine_pos ht)).comp t hs).mul hc using 1
  all_goals first | rfl | (dsimp [logSineProfileSlope]; ring)

theorem logSineProfile_curvature_neg {δ t : ℝ} (hδ : 0 ≤ δ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    deriv (logSineProfileSlope δ) t < 0 := by
  rw [(hasDerivAt_logSineProfileSlope ht).deriv]
  have hs := logSineProfile_sine_pos ht
  have hfirst : (-δ / (Real.sin (Real.pi * t) * (1 + Real.sin (Real.pi * t)) ^ 2)) *
      (Real.pi * Real.cos (Real.pi * t)) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ)
      (by positivity)) (sq_nonneg _)
  have hsecond : 0 < logSineLiftSlope δ (Real.sin (Real.pi * t)) * Real.pi ^ 2 *
      Real.sin (Real.pi * t) :=
    mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (logSineLiftSlope_ge_one hδ hs))
      (pow_pos Real.pi_pos 2)) hs
  linarith

theorem strictConcaveOn_logSineProfile {δ : ℝ} (hδ : 0 ≤ δ) :
    StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) (logSineProfile δ) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioo 0 1)
    ((continuousOn_logSineProfile δ).mono Ioo_subset_Icc_self)
  rw [interior_Ioo]
  have ha : StrictAntiOn (logSineProfileSlope δ) (Ioo (0 : ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
      (fun t ht => (hasDerivAt_logSineProfileSlope ht).continuousAt.continuousWithinAt)
    simpa only [interior_Ioo] using fun t ht => logSineProfile_curvature_neg hδ ht
  intro a ha' b hb hab
  rw [(hasDerivAt_logSineProfile ha').deriv, (hasDerivAt_logSineProfile hb).deriv]
  exact ha ha' hb hab


theorem two_mul_le_logSineProfile_sine {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    2 * t ≤ Real.sin (Real.pi * t) := by
  simpa only [show Real.pi / 2 * (2 * t) = Real.pi * t by ring] using
    Real.le_sin_mul (x := 2 * t) (by linarith) (by linarith)

theorem logSineProfile_endpoint_upper {δ t : ℝ} (hδ : 0 ≤ δ)
    (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    logSineProfile δ t ≤ Real.pi * t * (1 + δ * Real.log (1 / t)) := by
  have hs : 0 < Real.sin (Real.pi * t) := logSineProfile_sine_pos ⟨ht0, by linarith⟩
  have hlow := two_mul_le_logSineProfile_sine ht0.le ht
  have hup := Real.sin_le (mul_pos Real.pi_pos ht0).le
  have harg : 1 + 1 / Real.sin (Real.pi * t) ≤ 1 / t := by
    apply (le_div_iff₀ ht0).mpr
    have hh : t / Real.sin (Real.pi * t) ≤ 1 / 2 :=
      (div_le_iff₀ hs).mpr (by linarith)
    nlinarith [show 1 / Real.sin (Real.pi * t) * t = t / Real.sin (Real.pi * t) by ring]
  have hl := Real.log_le_log (by positivity : 0 < 1 + 1 / Real.sin (Real.pi * t)) harg
  have hln : 0 ≤ Real.log (1 + 1 / Real.sin (Real.pi * t)) :=
    Real.log_nonneg (by have := one_div_pos.mpr hs; linarith)
  rw [logSineProfile, logSineLift_eq hs]
  exact mul_le_mul hup (by nlinarith) (by positivity) (mul_pos Real.pi_pos ht0).le

theorem logSineProfile_endpoint_lower {δ t : ℝ} (hδ : 0 ≤ δ)
    (ht0 : 0 < t) (ht : t ≤ 1 / 2) (htp : Real.pi * t < 1) :
    2 * δ * t * Real.log (1 / (Real.pi * t)) ≤ logSineProfile δ t := by
  have hs : 0 < Real.sin (Real.pi * t) := logSineProfile_sine_pos ⟨ht0, by linarith⟩
  have hlow := two_mul_le_logSineProfile_sine ht0.le ht
  have hup := Real.sin_le (mul_pos Real.pi_pos ht0).le
  have hp : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
  have harg : 1 / (Real.pi * t) ≤ 1 + 1 / Real.sin (Real.pi * t) := by
    have hh : 1 / (Real.pi * t) ≤ 1 / Real.sin (Real.pi * t) := by
      exact (div_le_div_iff₀ hp hs).mpr (by simpa using hup)
    linarith
  have hl := Real.log_le_log (one_div_pos.mpr hp) harg
  have hln : 0 ≤ Real.log (1 / (Real.pi * t)) :=
    Real.log_nonneg ((le_div_iff₀ hp).mpr (by linarith))
  rw [logSineProfile, logSineLift_eq hs]
  calc
    2 * δ * t * Real.log (1 / (Real.pi * t)) =
        (2 * t) * (δ * Real.log (1 / (Real.pi * t))) := by ring
    _ ≤ Real.sin (Real.pi * t) * (δ * Real.log (1 + 1 / Real.sin (Real.pi * t))) :=
      mul_le_mul hlow (mul_le_mul_of_nonneg_left hl hδ) (mul_nonneg hδ hln) hs.le
    _ ≤ Real.sin (Real.pi * t) * (1 + δ * Real.log (1 + 1 / Real.sin (Real.pi * t))) := by
      nlinarith

end
end RHTower
