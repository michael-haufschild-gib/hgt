import GaloisForLFunctions.RHTower.MobiusWholeAnchorCapacityDisplacement
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Critical terminal-frame variance minimax

This module formalizes exact continuous variational core of Route E terminal-band law.
Exponential terminal weight on unit logarithmic band has positive mass and strictly positive
position variance. Every affine phase correction has exact Pythagorean decomposition into
centered variance plus a nonnegative centering defect. Consequently second-order phase correction
is unique, and first odd resonance has sharp coefficient pi squared times weighted variance.
-/

namespace RHTower

open MeasureTheory Set
open scoped Interval

noncomputable section

/-- Exponential terminal-position weight. -/
def routeETerminalWeight (a v : ℝ) : ℝ :=
  Real.exp (-a * v)

/-- Total terminal-band weight. -/
noncomputable def routeETerminalMass (a : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, routeETerminalWeight a v

/-- First terminal-position moment. -/
noncomputable def routeETerminalFirstMoment (a : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, routeETerminalWeight a v * v

/-- Weighted terminal-position mean. -/
noncomputable def routeETerminalMean (a : ℝ) : ℝ :=
  routeETerminalFirstMoment a / routeETerminalMass a

/-- Unnormalized terminal-position variance. -/
noncomputable def routeETerminalVariance (a : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1,
    routeETerminalWeight a v * (v - routeETerminalMean a) ^ 2

/-- Quadratic phase energy after an odd terminal resonance. Parameter u is resonance and b is
second-order correction. -/
noncomputable def routeETerminalQuadratic (a u b : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, routeETerminalWeight a v * (b - u * v) ^ 2

theorem continuous_routeETerminalWeight (a : ℝ) :
    Continuous (routeETerminalWeight a) := by
  unfold routeETerminalWeight
  fun_prop

theorem routeETerminalWeight_pos (a v : ℝ) :
    0 < routeETerminalWeight a v := by
  exact Real.exp_pos _

theorem routeETerminalMass_pos (a : ℝ) :
    0 < routeETerminalMass a := by
  unfold routeETerminalMass
  apply intervalIntegral.integral_pos (a := (0 : ℝ)) (b := 1) zero_lt_one
  · exact (continuous_routeETerminalWeight a).continuousOn
  · intro v hv
    exact (routeETerminalWeight_pos a v).le
  · exact ⟨0, Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩, routeETerminalWeight_pos a 0⟩

theorem routeETerminalMass_ne_zero (a : ℝ) :
    routeETerminalMass a ≠ 0 :=
  ne_of_gt (routeETerminalMass_pos a)

private theorem intervalIntegrable_routeETerminalWeight (a : ℝ) :
    IntervalIntegrable (routeETerminalWeight a) volume 0 1 :=
  (continuous_routeETerminalWeight a).intervalIntegrable 0 1

private theorem intervalIntegrable_routeETerminalWeight_mul_id (a : ℝ) :
    IntervalIntegrable (fun v : ℝ => routeETerminalWeight a v * v) volume 0 1 := by
  exact ((continuous_routeETerminalWeight a).mul continuous_id).intervalIntegrable 0 1

private theorem intervalIntegrable_routeETerminalCentered (a : ℝ) :
    IntervalIntegrable
      (fun v : ℝ => routeETerminalWeight a v * (v - routeETerminalMean a))
      volume 0 1 := by
  exact ((continuous_routeETerminalWeight a).mul
    (continuous_id.sub continuous_const)).intervalIntegrable 0 1

private theorem intervalIntegrable_routeETerminalVariance (a : ℝ) :
    IntervalIntegrable
      (fun v : ℝ => routeETerminalWeight a v * (v - routeETerminalMean a) ^ 2)
      volume 0 1 := by
  exact ((continuous_routeETerminalWeight a).mul
    ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable 0 1

/-- Weighted centered first moment vanishes exactly. -/
theorem integral_routeETerminalWeight_mul_centered (a : ℝ) :
    (∫ v in (0 : ℝ)..1,
      routeETerminalWeight a v * (v - routeETerminalMean a)) = 0 := by
  have hfun :
      (fun v : ℝ => routeETerminalWeight a v * (v - routeETerminalMean a)) =
        (fun v : ℝ =>
          routeETerminalWeight a v * v -
            routeETerminalMean a * routeETerminalWeight a v) := by
    funext v
    ring
  rw [hfun, intervalIntegral.integral_sub
    (intervalIntegrable_routeETerminalWeight_mul_id a)
    ((intervalIntegrable_routeETerminalWeight a).const_mul
      (routeETerminalMean a))]
  rw [intervalIntegral.integral_const_mul]
  change
    routeETerminalFirstMoment a -
      routeETerminalMean a * routeETerminalMass a = 0
  change
    routeETerminalFirstMoment a -
      (routeETerminalFirstMoment a / routeETerminalMass a) *
        routeETerminalMass a = 0
  field_simp [routeETerminalMass_ne_zero a]
  ring

/-- Terminal-position variance is strictly positive for every real exponential tilt. -/
theorem routeETerminalVariance_pos (a : ℝ) :
    0 < routeETerminalVariance a := by
  unfold routeETerminalVariance
  apply intervalIntegral.integral_pos (a := (0 : ℝ)) (b := 1) zero_lt_one
  · exact ((continuous_routeETerminalWeight a).mul
      ((continuous_id.sub continuous_const).pow 2)).continuousOn
  · intro v hv
    exact mul_nonneg (routeETerminalWeight_pos a v).le (sq_nonneg _)
  · by_cases hmean : routeETerminalMean a = 0
    · refine ⟨1, Set.mem_Icc.2 ⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [hmean]
      simpa [routeETerminalWeight] using Real.exp_pos (-a)
    · refine ⟨0, Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩, ?_⟩
      have hsq : 0 < (routeETerminalMean a) ^ 2 := sq_pos_of_ne_zero hmean
      simpa using mul_pos (routeETerminalWeight_pos a 0) hsq

/-- Exact weighted Pythagorean identity. It is source of unique second-order terminal phase
correction and sharp variance constant. -/
theorem routeETerminalQuadratic_eq_variance_add_centering
    (a u b : ℝ) :
    routeETerminalQuadratic a u b =
      routeETerminalMass a * (b - u * routeETerminalMean a) ^ 2 +
        u ^ 2 * routeETerminalVariance a := by
  let μ := routeETerminalMean a
  have hfun :
      (fun v : ℝ => routeETerminalWeight a v * (b - u * v) ^ 2) =
        (fun v : ℝ =>
          (b - u * μ) ^ 2 * routeETerminalWeight a v +
            u ^ 2 * (routeETerminalWeight a v * (v - μ) ^ 2) -
            (2 * u * (b - u * μ)) *
              (routeETerminalWeight a v * (v - μ))) := by
    funext v
    ring
  unfold routeETerminalQuadratic
  rw [hfun]
  have hweight := intervalIntegrable_routeETerminalWeight a
  have hvariance :
      IntervalIntegrable
        (fun v : ℝ => routeETerminalWeight a v * (v - μ) ^ 2)
        volume 0 1 := by
    simpa [μ] using intervalIntegrable_routeETerminalVariance a
  have hcentered :
      IntervalIntegrable
        (fun v : ℝ => routeETerminalWeight a v * (v - μ))
        volume 0 1 := by
    simpa [μ] using intervalIntegrable_routeETerminalCentered a
  have hterm1 :
      IntervalIntegrable
        (fun v : ℝ => (b - u * μ) ^ 2 * routeETerminalWeight a v)
        volume 0 1 :=
    hweight.const_mul ((b - u * μ) ^ 2)
  have hterm2 :
      IntervalIntegrable
        (fun v : ℝ => u ^ 2 * (routeETerminalWeight a v * (v - μ) ^ 2))
        volume 0 1 :=
    hvariance.const_mul (u ^ 2)
  have hleft :
      IntervalIntegrable
        (fun v : ℝ =>
          (b - u * μ) ^ 2 * routeETerminalWeight a v +
            u ^ 2 * (routeETerminalWeight a v * (v - μ) ^ 2))
        volume 0 1 :=
    hterm1.add hterm2
  have hright :
      IntervalIntegrable
        (fun v : ℝ =>
          (2 * u * (b - u * μ)) *
            (routeETerminalWeight a v * (v - μ)))
        volume 0 1 :=
    hcentered.const_mul (2 * u * (b - u * μ))
  rw [intervalIntegral.integral_sub
    hleft hright]
  rw [intervalIntegral.integral_add hterm1 hterm2,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [show μ = routeETerminalMean a by rfl,
    integral_routeETerminalWeight_mul_centered]
  simp only [mul_zero, sub_zero]
  unfold routeETerminalMass routeETerminalVariance
  ring

/-- Sharp lower bound for every second-order correction. -/
theorem routeETerminalVariance_minimax_lower (a u b : ℝ) :
    u ^ 2 * routeETerminalVariance a ≤ routeETerminalQuadratic a u b := by
  rw [routeETerminalQuadratic_eq_variance_add_centering]
  have hmass := (routeETerminalMass_pos a).le
  nlinarith [mul_nonneg hmass
    (sq_nonneg (b - u * routeETerminalMean a))]

/-- Exact equality condition: weighted correction must center terminal position. -/
theorem routeETerminalVariance_minimax_eq_iff (a u b : ℝ) :
    routeETerminalQuadratic a u b = u ^ 2 * routeETerminalVariance a ↔
      b = u * routeETerminalMean a := by
  rw [routeETerminalQuadratic_eq_variance_add_centering]
  have hmass := routeETerminalMass_pos a
  constructor
  · intro h
    have hzero :
        routeETerminalMass a * (b - u * routeETerminalMean a) ^ 2 = 0 := by
      linarith
    have hsquare : (b - u * routeETerminalMean a) ^ 2 = 0 :=
      (mul_eq_zero.1 hzero).resolve_left hmass.ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · rintro rfl
    ring_nf

/-- Unique global minimizer of correction coordinate. -/
theorem routeETerminalVariance_unique_minimizer (a u : ℝ) :
    (∀ b : ℝ,
      routeETerminalQuadratic a u (u * routeETerminalMean a) ≤
        routeETerminalQuadratic a u b) ∧
      ∀ b : ℝ,
        routeETerminalQuadratic a u b =
            routeETerminalQuadratic a u (u * routeETerminalMean a) →
          b = u * routeETerminalMean a := by
  have hcenter :
      routeETerminalQuadratic a u (u * routeETerminalMean a) =
        u ^ 2 * routeETerminalVariance a :=
    (routeETerminalVariance_minimax_eq_iff a u
      (u * routeETerminalMean a)).2 rfl
  constructor
  · intro b
    rw [hcenter]
    exact routeETerminalVariance_minimax_lower a u b
  · intro b hb
    apply (routeETerminalVariance_minimax_eq_iff a u b).1
    rwa [hcenter] at hb

/-- First odd terminal resonance has exact sharp coefficient pi squared times variance. -/
theorem routeETerminal_firstOddResonance_minimum (a : ℝ) :
    routeETerminalQuadratic a Real.pi
        (Real.pi * routeETerminalMean a) =
      Real.pi ^ 2 * routeETerminalVariance a :=
  (routeETerminalVariance_minimax_eq_iff a Real.pi
    (Real.pi * routeETerminalMean a)).2 rfl

/-- At flat terminal tilt, weighted mean is one half. -/
@[simp] theorem routeETerminalMean_zero :
    routeETerminalMean 0 = 1 / 2 := by
  simp [routeETerminalMean, routeETerminalFirstMoment,
    routeETerminalMass, routeETerminalWeight]

/-- At flat terminal tilt, unnormalized position variance is exactly one twelfth. -/
@[simp] theorem routeETerminalVariance_zero :
    routeETerminalVariance 0 = 1 / 12 := by
  rw [routeETerminalVariance]
  simp [routeETerminalWeight, routeETerminalMean_zero]
  have hcalc :
      (∫ v : ℝ in 0..1, (v - (1 / 2 : ℝ)) ^ 2) = (1 / 12 : ℝ) := by
    calc
      (∫ v : ℝ in 0..1, (v - (1 / 2 : ℝ)) ^ 2) =
        ∫ v : ℝ in 0..1, (v ^ 2 - v ^ 1 + (1 / 4 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        ring
      _ = 1 / 12 := by
        norm_num [intervalIntegral.integral_sub,
          intervalIntegral.integral_add, integral_pow,
          intervalIntegral.integral_const]
  convert hcalc using 1 <;> norm_num

/-- Critical endpoint exact constant pi squared over twelve. -/
theorem routeETerminal_firstOddResonance_minimum_zero :
    routeETerminalQuadratic 0 Real.pi (Real.pi / 2) =
      Real.pi ^ 2 / 12 := by
  rw [show Real.pi / 2 = Real.pi * routeETerminalMean 0 by
    rw [routeETerminalMean_zero]; ring]
  rw [routeETerminal_firstOddResonance_minimum, routeETerminalVariance_zero]
  ring

end

end RHTower
