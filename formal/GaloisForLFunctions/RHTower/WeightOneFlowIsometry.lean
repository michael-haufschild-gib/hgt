import Mathlib
import GaloisForLFunctions.RHTower.TransverseDensityWeightOne
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHalfDensityL1Completion

/-!
# The weight-one density is the square of the Meyer half-density weight

The corpus completes the literal Meyer cohomology with the `L¹` seminorm of weight
`exp (t/2)` in the logarithmic radius `t`, on which the centered dilation
`g(t) ↦ exp(−c/2) g(t − c)` is isometric.  The square of that weight is `exp t`, which is the
weight-one transverse density `du` of `TransverseDensityWeightOne` in the coordinate `u = exp t`.
This file records the identification, the `L²` isometry of the centered flow for the weight
`exp t`, and the converse: a continuous weight for which the centered flow is isometric on
intervals is a constant multiple of `exp t`.  So the polarization density of the Deninger–Singhof
structure and the corpus's half-density completion are the same weight, seen in `L²` and in `L¹`.
-/

open MeasureTheory Set

namespace RHTower

/-- The square of the Meyer half-density weight is the weight-one density in logarithmic
coordinates. -/
theorem deningerMeyerHalfDensityWeight_sq (t : ℝ) :
    deningerMeyerHalfDensityWeight t ^ (2 : ℕ) = Real.exp t := by
  unfold deningerMeyerHalfDensityWeight
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- **`L²` isometry of the centered flow for the weight-one density.** -/
theorem integral_exp_mul_normSq_centeredFlow (g : ℝ → ℂ) (c : ℝ) :
    ∫ t, Real.exp t * ‖Real.exp (-c / 2) * g (t - c)‖ ^ (2 : ℕ)
      = ∫ t, Real.exp t * ‖g t‖ ^ (2 : ℕ) := by
  have h : ∀ t, Real.exp t * ‖Real.exp (-c / 2) * g (t - c)‖ ^ (2 : ℕ)
      = (fun s => Real.exp s * ‖g s‖ ^ (2 : ℕ)) (t - c) := by
    intro t
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      mul_pow, ← Real.exp_nat_mul, Real.exp_sub]
    have h2 : Real.exp ((↑(2 : ℕ) : ℝ) * (-c / 2)) = (Real.exp c)⁻¹ := by
      rw [show (↑(2 : ℕ) : ℝ) * (-c / 2) = -c by push_cast; ring, Real.exp_neg]
    rw [h2, div_eq_mul_inv]
    ring
  simp_rw [h]
  exact integral_sub_right_eq_self (fun s => Real.exp s * ‖g s‖ ^ (2 : ℕ)) c

/-- **Uniqueness of the flow-isometric weight.**  A continuous weight for which the centered
flow preserves every interval mass is a constant multiple of `exp t`. -/
theorem weight_eq_exp_of_flow_isometry (w : ℝ → ℝ) (hw : Continuous w)
    (h : ∀ a b c : ℝ, ∫ t in a..b, Real.exp (-c) * w (t + c) = ∫ t in a..b, w t) (c : ℝ) :
    w c = w 0 * Real.exp c := by
  set f : ℝ → ℝ := fun t => Real.exp (-c) * w (t + c) - w t with hf
  have hfc : Continuous f := by
    unfold f
    fun_prop
  have hF : (fun b => ∫ t in (0 : ℝ)..b, f t) = fun _ => 0 := by
    funext b
    have h1 : IntervalIntegrable (fun t => Real.exp (-c) * w (t + c)) volume 0 b :=
      (by fun_prop : Continuous fun t => Real.exp (-c) * w (t + c)).intervalIntegrable 0 b
    have h2 : IntervalIntegrable w volume 0 b := hw.intervalIntegrable 0 b
    show ∫ t in (0 : ℝ)..b, (Real.exp (-c) * w (t + c) - w t) = 0
    rw [intervalIntegral.integral_sub h1 h2, h 0 b c, sub_self]
  have hd : HasDerivAt (fun b => ∫ t in (0 : ℝ)..b, f t) (f 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 0)
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt
  rw [hF] at hd
  have h0 : f 0 = 0 := hd.unique (hasDerivAt_const 0 (0 : ℝ))
  simp only [hf, zero_add] at h0
  have hexp : Real.exp (-c) * Real.exp c = 1 := by rw [← Real.exp_add]; simp
  calc w c = (Real.exp (-c) * w c) * Real.exp c := by
        rw [mul_assoc, mul_comm (w c), ← mul_assoc, hexp, one_mul]
    _ = w 0 * Real.exp c := by rw [sub_eq_zero.mp h0]

end RHTower
