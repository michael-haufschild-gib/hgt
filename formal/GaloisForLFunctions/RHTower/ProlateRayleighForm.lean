import GaloisForLFunctions.RHTower.ProlateBandSymmetric

/-!
# The prolate Rayleigh numerator as a quadratic form

Integration by parts on the band turns the prolate Rayleigh numerator into the manifestly negative
Dirichlet-plus-potential form

`∫_{−1}^{1} (P_c f)·f = −( ∫_{−1}^{1} (1−y²)·f′² + c²∫_{−1}^{1} y²·f² )` ,

with no boundary condition, since the Sturm–Liouville flux `(1−y²)f′` vanishes at `±1` on its own.

This is the form in which trial functions are tested: a trial function has prolate Rayleigh
numerator above `−K` times its squared norm exactly when its Dirichlet-plus-potential energy is
below `K` times that norm.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-- **The prolate Rayleigh numerator is minus the Dirichlet-plus-potential energy.** -/
theorem integral_prolateSLAction_mul_self {f : ℝ → ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hf2c : Continuous (deriv (deriv f))) (c : ℝ) :
    (∫ y in (-1 : ℝ)..1, prolateSLAction c f y * f y)
      = -((∫ y in (-1 : ℝ)..1, (1 - y ^ 2) * (deriv f y) ^ 2)
        + c ^ 2 * ∫ y in (-1 : ℝ)..1, y ^ 2 * f y ^ 2) := by
  have hf'c : Continuous (deriv f) := hf2.continuous
  have hfc : Continuous f := hf1.continuous
  have hA : IntervalIntegrable
      (fun y => f y * (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hB : IntervalIntegrable (fun y => f y * (c ^ 2 * y ^ 2 * f y)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  -- split the action into flux and potential
  have hsplit : (∫ y in (-1 : ℝ)..1, f y * prolateSLAction c f y)
      = (∫ y in (-1 : ℝ)..1,
          f y * (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y))
        - ∫ y in (-1 : ℝ)..1, f y * (c ^ 2 * y ^ 2 * f y) := by
    rw [← intervalIntegral.integral_sub hA hB]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [prolateSLAction]
    ring
  have hibp := band_flux_integral_by_parts hf2 hf2c hf1 hf'c
  have hcomm : (∫ y in (-1 : ℝ)..1, prolateSLAction c f y * f y)
      = ∫ y in (-1 : ℝ)..1, f y * prolateSLAction c f y :=
    intervalIntegral.integral_congr fun y _ => mul_comm _ _
  have hdir : (∫ y in (-1 : ℝ)..1, deriv f y * ((1 - y ^ 2) * deriv f y))
      = ∫ y in (-1 : ℝ)..1, (1 - y ^ 2) * (deriv f y) ^ 2 :=
    intervalIntegral.integral_congr fun y _ => by ring
  have hpot : (∫ y in (-1 : ℝ)..1, f y * (c ^ 2 * y ^ 2 * f y))
      = c ^ 2 * ∫ y in (-1 : ℝ)..1, y ^ 2 * f y ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  rw [hcomm, hsplit, hibp, hdir, hpot]
  ring

/-- **Trial criterion.**  A smooth trial function has prolate Rayleigh numerator above `−K` times
its squared aperture norm exactly when its Dirichlet-plus-potential energy is below `K` times that
norm. -/
theorem prolate_trial_gt_iff {f : ℝ → ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hf2c : Continuous (deriv (deriv f))) (c K : ℝ) :
    (-K * (∫ y in (-1 : ℝ)..1, f y * f y)
        < ∫ y in (-1 : ℝ)..1, prolateSLAction c f y * f y)
      ↔ (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) * (deriv f y) ^ 2)
          + c ^ 2 * (∫ y in (-1 : ℝ)..1, y ^ 2 * f y ^ 2)
        < K * ∫ y in (-1 : ℝ)..1, f y * f y := by
  rw [integral_prolateSLAction_mul_self hf1 hf2 hf2c]
  constructor
  · intro h
    linarith
  · intro h
    linarith

end RHTower
