import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralDescent

/-!
# Quantitative convergence without positive curvature

The actual flat L² gradient iteration has a telescoping dissipation
budget and a reciprocal energy bound. Its displacement from the
negative-part minimizer pays for every future energy decrease, despite
the potential's infinitely flat boundary.
-/

open MeasureTheory Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem integralEnergy_zero : integralEnergy (0 : Lp ℝ 2 μ) = 0 := by
  unfold integralEnergy
  calc
    (∫ x, potential ((0 : Lp ℝ 2 μ) x) ∂μ) = ∫ _, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      simp only [hx, Pi.zero_apply, potential_zero]
    _ = 0 := integral_zero _ _

private theorem energy_negativePart (f : Lp ℝ 2 μ) : integralEnergy (negativePartLp f) = 0 :=
  le_antisymm (by simpa only [integralEnergy_zero] using negativePartLp_minimizes f 0)
    (integral_energy_bounds _).1

/-- Energy decreases at every actual quotient-space iterate. -/
theorem descentLp_energy_step (f : Lp ℝ 2 μ) :
    integralEnergy (descentLp f) ≤ integralEnergy f := by
  have h := integralEnergy_unit_descent f
  change integralEnergy (descentLp f) ≤ integralEnergy f - ‖gradientLp f‖ ^ 2 / 2 at h
  linarith only [h, sq_nonneg ‖gradientLp f‖]

/-- Full finite dissipation, including the energy remaining after the last step. -/
theorem descentLp_dissipation_budget (f : Lp ℝ 2 μ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖gradientLp (descentLp^[k] f)‖ ^ 2) +
      2 * integralEnergy (descentLp^[n] f) ≤ 2 * integralEnergy f := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Function.iterate_zero_apply, zero_add, le_refl]
  | succ n ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    have h := integralEnergy_unit_descent (descentLp^[n] f)
    change integralEnergy (descentLp (descentLp^[n] f)) ≤
      integralEnergy (descentLp^[n] f) - ‖gradientLp (descentLp^[n] f)‖ ^ 2 / 2 at h
    linarith only [ih, h]

/-- The squared residual norms are summable, with their entire mass paid by the initial energy. -/
theorem descentLp_residual_summable (f : Lp ℝ 2 μ) :
    Summable (fun n : ℕ => ‖gradientLp (descentLp^[n] f)‖ ^ 2) ∧
      (∑' n : ℕ, ‖gradientLp (descentLp^[n] f)‖ ^ 2) ≤ 2 * integralEnergy f := by
  have hb (n : ℕ) : (∑ k ∈ Finset.range n, ‖gradientLp (descentLp^[k] f)‖ ^ 2) ≤
      2 * integralEnergy f := by
    linarith only [descentLp_dissipation_budget f n, (integral_energy_bounds (descentLp^[n] f)).1]
  exact ⟨summable_of_sum_range_le (fun _ => sq_nonneg _) hb,
    Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) hb⟩

private theorem step_energy_distance (x p : Lp ℝ 2 μ)
    (hp : integralEnergy p = 0) :
    2 * integralEnergy (descentLp x) + ‖descentLp x - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 := by
  have hs := integral_support p x
  rw [hp, show p - x = -(x - p) by abel, inner_neg_right] at hs
  have hd := integralEnergy_unit_descent x
  have he : descentLp x - p = (x - p) - gradientLp x := by unfold descentLp; abel
  rw [he, norm_sub_sq_real (x - p) (gradientLp x), real_inner_comm]
  change integralEnergy (descentLp x) ≤ integralEnergy x - ‖gradientLp x‖ ^ 2 / 2 at hd
  linarith only [hs, hd]

/-- Remaining energy and distance share one exact initial-distance budget. -/
theorem descentLp_energy_distance_budget (f : Lp ℝ 2 μ) (n : ℕ) :
    2 * (n : ℝ) * integralEnergy (descentLp^[n] f) +
      ‖descentLp^[n] f - negativePartLp f‖ ^ 2 ≤ ‖f - negativePartLp f‖ ^ 2 := by
  induction n with
  | zero => simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, Function.iterate_zero_apply, le_refl]
  | succ n ih =>
    have hs := step_energy_distance (descentLp^[n] f) (negativePartLp f) (energy_negativePart f)
    have hd := mul_le_mul_of_nonneg_left (descentLp_energy_step (descentLp^[n] f))
      (show (0 : ℝ) ≤ 2 * n by positivity)
    rw [Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one]
    linarith only [ih, hs, hd]

/-- A reciprocal energy rate holds without strong convexity or a spectral gap. -/
theorem descentLp_energy_rate (f : Lp ℝ 2 μ) (n : ℕ) :
    integralEnergy (descentLp^[n + 1] f) ≤
      ‖f - negativePartLp f‖ ^ 2 / (2 * ((n : ℝ) + 1)) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
  have h := descentLp_energy_distance_budget f (n + 1)
  simp only [Nat.cast_add, Nat.cast_one] at h
  nlinarith only [h, sq_nonneg ‖descentLp^[n + 1] f - negativePartLp f‖]

#print axioms descentLp_dissipation_budget
#print axioms descentLp_residual_summable
#print axioms descentLp_energy_distance_budget
#print axioms descentLp_energy_rate
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
