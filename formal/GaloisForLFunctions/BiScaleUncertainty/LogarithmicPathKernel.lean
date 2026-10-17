import GaloisForLFunctions.BiScaleUncertainty.SobolevLogarithmicTransport
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measurable logarithmic paths and exact local energy slack

An edge joins `u` to `u+h`; its additive resistance is the distance between the
physical endpoints. The associated interval kernel transports genuine L2
velocity energy. Every local jump is bounded by its path budget, and the
nonnegative extended slack records exactly the difference.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

abbrev Edge := ℝ × ℝ

def lower (e : Edge) : ℝ := min e.2 (e.2+e.1)
def upper (e : Edge) : ℝ := max e.2 (e.2+e.1)
def resistance (e : Edge) : ℝ := Real.exp (upper e)-Real.exp (lower e)

theorem lower_le_upper (e : Edge) : lower e ≤ upper e := min_le_max

theorem resistance_nonneg (e : Edge) : 0 ≤ resistance e :=
  sub_nonneg.mpr (Real.exp_le_exp.mpr (lower_le_upper e))

theorem measurable_lower : Measurable lower :=
  measurable_snd.min (measurable_snd.add measurable_fst)

theorem measurable_upper : Measurable upper :=
  measurable_snd.max (measurable_snd.add measurable_fst)

theorem measurable_resistance : Measurable resistance :=
  (Real.continuous_exp.measurable.comp measurable_upper).sub
    (Real.continuous_exp.measurable.comp measurable_lower)

def pathKernel (e : Edge) (y : ℝ) : ℝ≥0∞ :=
  (Ioc (lower e) (upper e)).indicator (fun _ => ENNReal.ofReal (resistance e)) y

theorem measurable_pathKernel : Measurable (Function.uncurry pathKernel) := by
  have hs : MeasurableSet {p : Edge × ℝ | lower p.1 < p.2 ∧ p.2 ≤ upper p.1} :=
    (measurableSet_lt (measurable_lower.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_upper.comp measurable_fst))
  exact ((measurable_resistance.comp measurable_fst).ennreal_ofReal).indicator hs

theorem measurable_pathKernel_right (e : Edge) : Measurable (pathKernel e) :=
  measurable_pathKernel.comp (measurable_const.prodMk measurable_id)

theorem measurable_pathKernel_left (y : ℝ) : Measurable (fun e => pathKernel e y) :=
  measurable_pathKernel.comp (measurable_id.prodMk measurable_const)

def velocityDensity (q : Velocity) (x : ℝ) : ℝ := Real.exp x*(q (Real.exp x))^2

theorem velocityDensity_nonneg (q : Velocity) (x : ℝ) : 0 ≤ velocityDensity q x :=
  mul_nonneg (Real.exp_pos x).le (sq_nonneg _)

theorem measurable_velocityDensity (q : Velocity) : Measurable (velocityDensity q) := by
  have hq := (Lp.stronglyMeasurable q).measurable
  unfold velocityDensity
  fun_prop

theorem ae_velocityDensity_eq_derivative (q : Velocity) :
    velocityDensity q =ᵐ[volume] fun x => Real.exp (-x)*(deriv (logPrimitive q) x)^2 := by
  filter_upwards [ae_deriv_logPrimitive q] with x hx
  rw [hx, logVelocity, velocityDensity, Real.exp_neg]
  field_simp

theorem intervalIntegrable_velocityDensity (q : Velocity) (a b : ℝ) :
    IntervalIntegrable (velocityDensity q) volume a b :=
  (intervalIntegrable_logDerivativeEnergy q a b).congr_ae
    (ae_restrict_of_ae (ae_velocityDensity_eq_derivative q).symm)

theorem integral_velocityDensity (q : Velocity) (a b : ℝ) :
    (∫ x in a..b, velocityDensity q x) = energy q (Real.exp a) (Real.exp b) :=
  exp_substitution (fun t => (q t)^2) a b

def density (q : Velocity) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (velocityDensity q x)

theorem measurable_density (q : Velocity) : Measurable (density q) :=
  (measurable_velocityDensity q).ennreal_ofReal

private theorem lintegral_density_Ioc (q : Velocity) (a b : ℝ) (hab : a ≤ b) :
    (∫⁻ y in Ioc a b, density q y) = ENNReal.ofReal (energy q (Real.exp a) (Real.exp b)) := by
  rw [← integral_velocityDensity q a b, intervalIntegral.integral_of_le hab]
  exact (ofReal_integral_eq_lintegral_ofReal
    (intervalIntegrable_velocityDensity q a b).1
    (Eventually.of_forall (velocityDensity_nonneg q))).symm

def budget (q : Velocity) (e : Edge) : ℝ≥0∞ := ∫⁻ y, pathKernel e y*density q y

theorem measurable_budget (q : Velocity) : Measurable (budget q) :=
  (measurable_pathKernel.mul ((measurable_density q).comp measurable_snd)).lintegral_prod_right

/-- The extended path budget is the finite physical resistance times interval energy. -/
theorem budget_eq_physical (q : Velocity) (e : Edge) :
    budget q e = ENNReal.ofReal (resistance e) *
      ENNReal.ofReal (energy q (Real.exp (lower e)) (Real.exp (upper e))) := by
  calc
    _ = ∫⁻ y in Ioc (lower e) (upper e), ENNReal.ofReal (resistance e)*density q y := by
      rw [← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro y
      by_cases h : y ∈ Ioc (lower e) (upper e)
      · simp [pathKernel, h]
      · simp [pathKernel, h]
    _ = _ := by
      rw [lintegral_const_mul _ (measurable_density q),
        lintegral_density_Ioc q (lower e) (upper e) (lower_le_upper e)]

/-- Every individual edge has a finite budget even when total graph energy diverges. -/
theorem budget_ne_top (q : Velocity) (e : Edge) : budget q e ≠ ∞ := by
  rw [budget_eq_physical]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem continuous_logPrimitive (q : Velocity) : Continuous (logPrimitive q) :=
  (intervalIntegral.continuous_primitive (intervalIntegrable_velocity q) 0).comp
    Real.continuous_exp

def jump (q : Velocity) (e : Edge) : ℝ≥0∞ :=
  ENNReal.ofReal ((logPrimitive q (e.2+e.1)-logPrimitive q e.2)^2)

theorem measurable_jump (q : Velocity) : Measurable (jump q) := by
  have hf := (continuous_logPrimitive q).measurable
  unfold jump
  fun_prop

theorem jump_le_budget (q : Velocity) (e : Edge) : jump q e ≤ budget q e := by
  have ht : Real.exp (lower e)+resistance e =
      Real.exp (upper e) := by
    dsimp [resistance]
    ring
  have h := increment_sq_le_energy q (Real.exp (lower e))
    ⟨resistance e, resistance_nonneg e⟩
  change (primitive q (Real.exp (lower e)+resistance e)-primitive q (Real.exp (lower e)))^2 ≤
    resistance e * energy q (Real.exp (lower e)) (Real.exp (lower e)+resistance e) at h
  rw [ht] at h
  have hj : (logPrimitive q (e.2+e.1)-logPrimitive q e.2)^2 =
      (primitive q (Real.exp (upper e))-primitive q (Real.exp (lower e)))^2 := by
    rcases le_total e.2 (e.2+e.1) with he | he
    · simp [lower, upper, min_eq_left he, max_eq_right he, logPrimitive]
    · simp only [lower, upper, min_eq_right he, max_eq_left he, logPrimitive]
      ring
  rw [jump, hj, budget_eq_physical, ← ENNReal.ofReal_mul (resistance_nonneg e)]
  exact ENNReal.ofReal_le_ofReal h

def slack (q : Velocity) (e : Edge) : ℝ≥0∞ := budget q e-jump q e

theorem measurable_slack (q : Velocity) : Measurable (slack q) :=
  (measurable_budget q).sub (measurable_jump q)

/-- Addition exposes the exact defect without subtracting infinite total energies. -/
theorem jump_add_slack (q : Velocity) (e : Edge) : jump q e+slack q e = budget q e :=
  add_tsub_cancel_of_le (jump_le_budget q e)

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
