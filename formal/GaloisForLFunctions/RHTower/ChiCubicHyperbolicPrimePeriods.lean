import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeVariation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Complete phase periods of the actual frozen cubic amplitude

The nonoscillatory amplitude is frozen at its original prime anchor. Both
gap signs give exact cancellation on every complete integer-radius phase cell.
-/

noncomputable section

namespace RHTower

open MeasureTheory

private theorem integral_oscillation_symmetric (k R : ℝ) (hk : k ≠ 0) :
    (∫ x in (-R)..R, bourgainOscillation (k * x)) =
      k⁻¹ • (2 * (Real.sin (k * R) : ℂ)) := by
  have h : (∫ x in (-(k * R))..(k * R), bourgainOscillation x) =
      2 * (Real.sin (k * R) : ℂ) := by
    simpa only [bourgainOscillation, mul_comm] using integral_exp_mul_I_eq_sin (k * R)
  rw [intervalIntegral.integral_comp_mul_left _ hk, mul_neg, h]

/-- The literal amplitude frozen at its anchor has zero integral over every
complete integer-radius hyperbolic phase cell. Both signs of the gap are kept. -/
theorem chiCubicHyperbolicPrimeAmplitude_frozen_period (N : ℝ) (M p r : ℕ) :
    (∫ x in Set.Icc
        ((r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r|)
        ((r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r|),
      chiCubicHyperbolicPrimeAmplitude N (p, r) r *
        bourgainOscillation (2 * Real.pi * (((p : ℝ) - r) * (x - r) / r))) = 0 := by
  by_cases hrz : r = 0
  · subst r
    simp
  by_cases hne : p = r
  · subst p
    simp
  have hr : 0 < r := Nat.pos_of_ne_zero hrz
  let R : ℝ := (M : ℝ) * r / |(p : ℝ) - r|
  let k : ℝ := 2 * Real.pi * ((p : ℝ) - r) / r
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have ha : (p : ℝ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hk : k ≠ 0 := by
    dsimp [k]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_pos.ne') ha) hr0.ne'
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsin : Real.sin (k * R) = 0 := by
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have hangle : k * R = -(((2 * M : ℕ) : ℝ) * Real.pi) := by
        dsimp [k, R]
        rw [abs_of_neg hneg]
        push_cast
        field_simp
      rw [hangle, Real.sin_neg, Real.sin_nat_mul_pi, neg_zero]
    · have hangle : k * R = ((2 * M : ℕ) : ℝ) * Real.pi := by
        dsimp [k, R]
        rw [abs_of_pos hpos]
        push_cast
        field_simp
      rw [hangle, Real.sin_nat_mul_pi]
  have he : (fun x : ℝ => bourgainOscillation
      (2 * Real.pi * (((p : ℝ) - r) * (x - r) / r))) =
      (fun x : ℝ => bourgainOscillation (k * (x - r))) := by
    funext x
    congr 1
    dsimp [k]
    ring
  change (∫ x in Set.Icc ((r : ℝ) - R) ((r : ℝ) + R),
    chiCubicHyperbolicPrimeAmplitude N (p, r) r *
      bourgainOscillation (2 * Real.pi * (((p : ℝ) - r) * (x - r) / r))) = 0
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const_mul, he,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => bourgainOscillation (k * x))]
  rw [show (r : ℝ) - R - r = -R by ring, show (r : ℝ) + R - r = R by ring,
    integral_oscillation_symmetric k R hk, hsin, Complex.ofReal_zero, mul_zero,
    smul_zero, mul_zero]

end RHTower
