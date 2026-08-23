import GaloisForLFunctions.HTGeometry.SteinhausIntervalBridge
import GaloisForLFunctions.RHTower.BesselIZeroUpperBound
import GaloisForLFunctions.RHTower.BesselIZeroLowerBound

/-!
# The circle Laplace transform is the modified Bessel function

`steinhausLaplace r = besselI0 r`.  Shifting the cosine to a sine and folding the second half
period onto the first turns the circle average into the corpus's Bessel integral, which already
carries both sharp envelopes.
-/

open MeasureTheory Set

namespace HTGeometry

open GaloisForLFunctions.RHTower

noncomputable section

theorem integral_exp_cos_eq_exp_sin (r : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.cos t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.sin t) := by
  have hper : Function.Periodic (fun s : ℝ => Real.exp (r * Real.sin s)) (2 * Real.pi) := by
    intro s
    simp [Real.sin_add_two_pi]
  have hshift : (∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.sin (t + Real.pi / 2)))
      = ∫ s in (0 + Real.pi / 2)..(2 * Real.pi + Real.pi / 2), Real.exp (r * Real.sin s) :=
    intervalIntegral.integral_comp_add_right (fun s : ℝ => Real.exp (r * Real.sin s))
      (Real.pi / 2)
  have hcos : ∀ t : ℝ, Real.sin (t + Real.pi / 2) = Real.cos t := fun t => Real.sin_add_pi_div_two t
  have hleft : (∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.cos t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.sin (t + Real.pi / 2)) :=
    intervalIntegral.integral_congr fun t _ => by rw [hcos t]
  rw [hleft, hshift, show (0 : ℝ) + Real.pi / 2 = Real.pi / 2 by ring,
    show 2 * Real.pi + Real.pi / 2 = Real.pi / 2 + 2 * Real.pi by ring]
  have hperiod := hper.intervalIntegral_add_eq (Real.pi / 2) 0
  simpa using hperiod

theorem integral_exp_sin_fold (r : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.sin t))
      = 2 * ∫ t in (0 : ℝ)..Real.pi, Real.cosh (r * Real.sin t) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsplit : (∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.sin t))
      = (∫ t in (0 : ℝ)..Real.pi, Real.exp (r * Real.sin t))
        + ∫ t in Real.pi..(2 * Real.pi), Real.exp (r * Real.sin t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sin)).intervalIntegrable
        _ _
    · exact (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sin)).intervalIntegrable
        _ _
  have hsecond : (∫ t in Real.pi..(2 * Real.pi), Real.exp (r * Real.sin t))
      = ∫ u in (0 : ℝ)..Real.pi, Real.exp (-(r * Real.sin u)) := by
    have hshift : (∫ u in (0 : ℝ)..Real.pi, Real.exp (r * Real.sin (u + Real.pi)))
        = ∫ s in (0 + Real.pi)..(Real.pi + Real.pi), Real.exp (r * Real.sin s) :=
      intervalIntegral.integral_comp_add_right (fun s : ℝ => Real.exp (r * Real.sin s)) Real.pi
    have hcongr : (∫ u in (0 : ℝ)..Real.pi, Real.exp (r * Real.sin (u + Real.pi)))
        = ∫ u in (0 : ℝ)..Real.pi, Real.exp (-(r * Real.sin u)) :=
      intervalIntegral.integral_congr fun u _ => by
        rw [Real.sin_add_pi]
        ring_nf
    rw [← hcongr, hshift]
    congr 1
    · ring
    · ring
  have hint1 : IntervalIntegrable (fun t : ℝ => Real.exp (r * Real.sin t)) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hint2 : IntervalIntegrable (fun t : ℝ => Real.exp (-(r * Real.sin t))) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [hsplit, hsecond, ← intervalIntegral.integral_add hint1 hint2,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [Real.cosh_eq]
  ring

/-- **The circle Laplace transform is `I₀`.** -/
theorem steinhausLaplace_eq_besselI0 (r : ℝ) : steinhausLaplace r = besselI0 r := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [steinhausLaplace_eq_intervalIntegral, integral_exp_cos_eq_exp_sin,
    integral_exp_sin_fold, besselI0]
  field_simp

/-- **The sharp upper envelope of the circle cumulant.** -/
theorem steinhausLogLaplace_le {x : ℝ} (hx : 0 < x) :
    steinhausLogLaplace x ≤ x + Real.log (Real.sqrt (Real.pi / (2 * x))) := by
  have hbound := besselI0_le_exp_div_sqrt hx
  rw [← steinhausLaplace_eq_besselI0] at hbound
  have hLpos := steinhausLaplace_pos x
  have hcpos : (0 : ℝ) < Real.sqrt (Real.pi / (2 * x)) := by
    have : (0 : ℝ) < Real.pi / (2 * x) := by positivity
    exact Real.sqrt_pos.2 this
  rw [steinhausLogLaplace]
  refine (Real.log_le_log hLpos hbound).trans (le_of_eq ?_)
  rw [Real.log_mul (Real.exp_pos x).ne' hcpos.ne', Real.log_exp]

/-- **The sharp lower envelope of the circle cumulant.** -/
theorem le_steinhausLogLaplace_sharp {x : ℝ} (hx : 1 ≤ x) :
    x - Real.log (2 * Real.pi * Real.sqrt x) ≤ steinhausLogLaplace x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hx0 : (0 : ℝ) < x := by linarith
  have hbound := exp_div_le_besselI0 hx
  rw [← steinhausLaplace_eq_besselI0] at hbound
  have hLpos := steinhausLaplace_pos x
  have hden : (0 : ℝ) < 2 * Real.pi * Real.sqrt x := by
    have : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
    positivity
  rw [steinhausLogLaplace]
  refine le_trans (le_of_eq ?_) (Real.log_le_log (by positivity) hbound)
  rw [Real.log_div (Real.exp_pos x).ne' hden.ne', Real.log_exp]

end

end HTGeometry
