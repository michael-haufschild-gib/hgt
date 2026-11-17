import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A flat convex potential with controlled tangent error

The flat potential in §2.4 of arXiv:2611.08616, with exponent one, is
the second primitive of `expNegInvGlue`. Its curvature lies in `[0,1]`.
Consequently its gradient is a monotone contraction and its tangent error
lies between zero and half the squared displacement. These are pointwise
nonlinear tests for jump energies; no positivity of a Weil form is assumed.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex

open Set MeasureTheory
noncomputable section

/-- Gradient of the flat potential. -/
def gradient (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, expNegInvGlue u

/-- The twice-integrated flat curvature. -/
def potential (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, gradient u

@[simp] theorem gradient_zero : gradient 0 = 0 := by simp only [gradient, intervalIntegral.integral_same]

@[simp] theorem potential_zero : potential 0 = 0 := by simp only [potential, intervalIntegral.integral_same]

private theorem continuous_curvature : Continuous expNegInvGlue :=
  (expNegInvGlue.contDiff (n := 0)).continuous

theorem gradient_hasDerivAt (t : ℝ) : HasDerivAt gradient (expNegInvGlue t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_curvature.intervalIntegrable 0 t)
    (continuous_curvature.stronglyMeasurableAtFilter _ _)
    continuous_curvature.continuousAt

private theorem differentiable_gradient : Differentiable ℝ gradient :=
  fun t => (gradient_hasDerivAt t).differentiableAt

theorem potential_hasDerivAt (t : ℝ) : HasDerivAt potential (gradient t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (differentiable_gradient.continuous.intervalIntegrable 0 t)
    (differentiable_gradient.continuous.stronglyMeasurableAtFilter _ _)
    differentiable_gradient.continuous.continuousAt

private theorem differentiable_potential : Differentiable ℝ potential :=
  fun t => (potential_hasDerivAt t).differentiableAt

theorem gradient_contDiff (n : ℕ∞) : ContDiff ℝ n gradient := by
  apply contDiff_all_iff_nat.2 (fun k => ?_) n
  cases k with
  | zero => exact contDiff_zero.2 differentiable_gradient.continuous
  | succ k =>
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = k + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_gradient, by simp, ?_⟩
    have hd : deriv gradient = expNegInvGlue := funext fun t => (gradient_hasDerivAt t).deriv
    rw [hd]
    exact expNegInvGlue.contDiff

/-- The flat junction survives both integrations to every finite order. -/
theorem potential_contDiff (n : ℕ∞) : ContDiff ℝ n potential := by
  apply contDiff_all_iff_nat.2 (fun k => ?_) n
  cases k with
  | zero => exact contDiff_zero.2 differentiable_potential.continuous
  | succ k =>
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = k + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_potential, by simp, ?_⟩
    have hd : deriv potential = gradient := funext fun t => (potential_hasDerivAt t).deriv
    rw [hd]
    exact gradient_contDiff k

theorem curvature_bounds (t : ℝ) : 0 ≤ expNegInvGlue t ∧ expNegInvGlue t ≤ 1 := by
  refine ⟨expNegInvGlue.nonneg t, ?_⟩
  by_cases ht : t ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos ht]
    norm_num
  · rw [expNegInvGlue, if_neg ht, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge ht))

theorem gradient_monotone : Monotone gradient := by
  apply monotone_of_deriv_nonneg differentiable_gradient
  intro t
  rw [(gradient_hasDerivAt t).deriv]
  exact (curvature_bounds t).1

theorem gradient_zero_on_negative (t : ℝ) : gradient (-|t|) = 0 := by
  unfold gradient
  calc
    (∫ u in (0 : ℝ)..(-|t|), expNegInvGlue u) = ∫ _ in (0 : ℝ)..(-|t|), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_ge (neg_nonpos.mpr (abs_nonneg t))] at hu
      exact expNegInvGlue.zero_of_nonpos hu.2
    _ = 0 := intervalIntegral.integral_zero

theorem potential_zero_on_negative (t : ℝ) : potential (-|t|) = 0 := by
  unfold potential
  calc
    (∫ u in (0 : ℝ)..(-|t|), gradient u) = ∫ _ in (0 : ℝ)..(-|t|), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_ge (neg_nonpos.mpr (abs_nonneg t))] at hu
      have he : -|u| = u := by rw [abs_of_nonpos hu.2]; ring
      simpa only [he] using gradient_zero_on_negative u
    _ = 0 := intervalIntegral.integral_zero

theorem gradient_nonneg (t : ℝ) : 0 ≤ gradient t := by
  have h := gradient_monotone (neg_abs_le t)
  rwa [gradient_zero_on_negative] at h

/-- The flat gradient is an admissible scalar contraction fixing zero. -/
theorem gradient_contraction : LipschitzWith 1 gradient := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_gradient
  intro t
  change ‖deriv gradient t‖ ≤ (1 : ℝ)
  rw [(gradient_hasDerivAt t).deriv, Real.norm_eq_abs,
    abs_of_nonneg (curvature_bounds t).1]
  exact (curvature_bounds t).2

theorem potential_convex : ConvexOn ℝ univ potential := by
  apply Monotone.convexOn_univ_of_deriv differentiable_potential
  simpa only [show deriv potential = gradient from
    funext fun t => (potential_hasDerivAt t).deriv] using gradient_monotone

/-- The gradient grows no faster than the square root of twice its potential. -/
theorem gradient_square_le (t : ℝ) : gradient t ^ 2 ≤ 2 * potential t := by
  have hd (x : ℝ) : HasDerivAt (fun u => 2 * potential u - gradient u ^ 2)
      (2 * gradient x * (1 - expNegInvGlue x)) x := by
    have h := ((potential_hasDerivAt x).const_mul 2).fun_sub
      ((gradient_hasDerivAt x).pow 2)
    change HasDerivAt (fun u => 2 * potential u - gradient u ^ 2)
      (2 * gradient x - 2 * gradient x ^ 1 * expNegInvGlue x) x at h
    have he : 2 * gradient x - 2 * gradient x ^ 1 * expNegInvGlue x =
        2 * gradient x * (1 - expNegInvGlue x) := by ring
    rwa [he] at h
  have hm : Monotone (fun u => 2 * potential u - gradient u ^ 2) := by
    apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    exact mul_nonneg (mul_nonneg (by norm_num) (gradient_nonneg x))
      (sub_nonneg.mpr (curvature_bounds x).2)
  have h := hm (neg_abs_le t)
  dsimp only at h
  rw [potential_zero_on_negative, gradient_zero_on_negative] at h
  nlinarith only [h]

/-- A global quadratic upper bound for both orientations of the tangent error. -/
theorem tangent_error_bounds (x y : ℝ) :
    0 ≤ potential x - potential y - gradient y * (x - y) ∧
      potential x - potential y - gradient y * (x - y) ≤ (x - y) ^ 2 / 2 := by
  have support {f : ℝ → ℝ} {d : ℝ} (hc : ConvexOn ℝ univ f) (hd : HasDerivAt f d y) :
      d * (x - y) ≤ f x - f y := by
    rcases lt_trichotomy y x with h | rfl | h
    · have hs := hc.le_slope_of_hasDerivAt (mem_univ y) (mem_univ x) h hd
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
      exact hs
    · simp only [sub_self, mul_zero, le_refl]
    · have hs := hc.slope_le_of_hasDerivAt (mem_univ x) (mem_univ y) h hd
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
      nlinarith only [hs]
  have hc := support potential_convex (potential_hasDerivAt y)
  have hd (t : ℝ) : HasDerivAt (fun u => u ^ 2 / 2 - potential u) (t - gradient t) t := by
    have h := (((hasDerivAt_id t).pow 2).div_const 2).fun_sub
      (potential_hasDerivAt t)
    change HasDerivAt (fun u => u ^ 2 / 2 - potential u)
      ((2 * t ^ 1 * 1) / 2 - gradient t) t at h
    have he : (2 * t ^ 1 * 1) / 2 - gradient t = t - gradient t := by ring
    rwa [he] at h
  have hm : Monotone (fun t => t - gradient t) := by
    apply monotone_of_deriv_nonneg
      (fun t => ((hasDerivAt_id t).fun_sub (gradient_hasDerivAt t)).differentiableAt)
    intro t
    rw [((hasDerivAt_id t).fun_sub (gradient_hasDerivAt t)).deriv]
    exact sub_nonneg.mpr (curvature_bounds t).2
  have hconv : ConvexOn ℝ univ (fun u => u ^ 2 / 2 - potential u) := by
    apply Monotone.convexOn_univ_of_deriv (fun t => (hd t).differentiableAt)
    simpa only [show deriv (fun u => u ^ 2 / 2 - potential u) =
      (fun t => t - gradient t) from funext fun t => (hd t).deriv] using hm
  have hu := support hconv (hd y)
  constructor <;> nlinarith only [hc, hu]

/-- The potential has a global quadratic majorant and is nonnegative. -/
theorem potential_bounds (t : ℝ) : 0 ≤ potential t ∧ potential t ≤ t ^ 2 / 2 := by
  simpa only [potential_zero, gradient_zero, sub_zero, zero_mul] using tangent_error_bounds t 0

/-- The jump pairing lies between the transformed and original squared jumps. -/
theorem jump_bounds (a b : ℝ) :
    (gradient a - gradient b) ^ 2 ≤ (a - b) * (gradient a - gradient b) ∧
      (a - b) * (gradient a - gradient b) ≤ (a - b) ^ 2 := by
  have hl : |gradient a - gradient b| ≤ |a - b| := by
    simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using
      gradient_contraction.norm_sub_le a b
  rcases le_total b a with h | h
  · have hx := sub_nonneg.mpr h
    have hy := sub_nonneg.mpr (gradient_monotone h)
    rw [abs_of_nonneg hx, abs_of_nonneg hy] at hl
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_right hl hy]
    · nlinarith only [mul_le_mul_of_nonneg_left hl hx]
  · have hx := sub_nonpos.mpr h
    have hy := sub_nonpos.mpr (gradient_monotone h)
    rw [abs_of_nonpos hx, abs_of_nonpos hy] at hl
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_right hl (neg_nonneg.mpr hy)]
    · nlinarith only [mul_le_mul_of_nonneg_left hl (neg_nonneg.mpr hx)]

/-- The flat transform and its complement split every squared jump contractively. -/
theorem complementary_jump_bound (a b : ℝ) :
    (gradient a - gradient b) ^ 2 +
      ((a - gradient a) - (b - gradient b)) ^ 2 ≤ (a - b) ^ 2 := by
  nlinarith only [(jump_bounds a b).1]

#print axioms potential_contDiff
#print axioms gradient_contraction
#print axioms potential_convex
#print axioms gradient_square_le
#print axioms tangent_error_bounds
#print axioms jump_bounds
#print axioms complementary_jump_bound

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
