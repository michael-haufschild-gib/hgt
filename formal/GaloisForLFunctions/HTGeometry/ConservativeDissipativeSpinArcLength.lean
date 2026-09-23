import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Exact arclength of conservative–dissipative spin precession

The Schaffer–Exl spin mechanism (arXiv:2609.04530), combined with the corpus's
Böttcher/Marty conformality identity, gives an arctangent remaining-length
potential. Its derivative is minus the actual spin speed, and its vanishing
limit yields the exact finite improper integral of speed. Positive damping
is constructed exponentially; initial coordinates and times are unrestricted.
-/

set_option autoImplicit false
open scoped Matrix RealInnerProductSpace
open Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Radius differentiation is valid even at the stationary zero chart coordinate. -/
theorem hasDerivAt_spinPlaneFlow_norm (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun v => ‖spinPlaneFlow a z v‖) (-a ^ (2 : ℕ) * ‖spinPlaneFlow a z t‖) t := by
  have h := (((hasDerivAt_id t).const_mul (-a ^ (2 : ℕ))).exp).mul_const ‖z‖
  simp only [spinPlaneFlow_norm]
  simpa only [id_eq, mul_one, mul_assoc, mul_left_comm, mul_comm] using h

/-- Explicit continuous speed of the actual sphere-valued spin trajectory. -/
theorem continuous_spinSphereFlow_speed (a : ℝ) (z : ℂ) :
    Continuous (fun t => ‖spinSphereField a (spinSphereFlow a z t)‖) := by
  have hr : Continuous (fun t => ‖spinPlaneFlow a z t‖) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_spinPlaneFlow_norm a z t).continuousAt)
  have hn := (hr.const_mul ‖spinPlaneRate a‖).const_mul (2 : ℝ)
  have hd : Continuous (fun t => 1 + ‖spinPlaneFlow a z t‖ ^ (2 : ℕ)) := continuous_const.add (hr.pow 2)
  have h := hn.div hd (fun t => by positivity : ∀ t : ℝ, 1 + ‖spinPlaneFlow a z t‖ ^ (2 : ℕ) ≠ 0)
  convert h using 1
  funext t
  rw [spinSphereFlow_speed, norm_mul]
  rfl

/-- Arctangent radius is an exact remaining-length potential under constructed positive damping. -/
def spinRemainingLength (s : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  (2 * ‖spinPlaneRate (Real.exp s)‖ / (Real.exp s) ^ (2 : ℕ)) *
    Real.arctan ‖spinPlaneFlow (Real.exp s) z t‖

/-- The remaining-length potential loses exactly the actual Euclidean spin speed. -/
theorem hasDerivAt_spinRemainingLength (s : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (spinRemainingLength s z)
      (-‖spinSphereField (Real.exp s) (spinSphereFlow (Real.exp s) z t)‖) t := by
  have h := ((hasDerivAt_spinPlaneFlow_norm (Real.exp s) z t).arctan).const_mul
    (2 * ‖spinPlaneRate (Real.exp s)‖ / (Real.exp s) ^ (2 : ℕ))
  change HasDerivAt (fun v => (2 * ‖spinPlaneRate (Real.exp s)‖ / (Real.exp s) ^ (2 : ℕ)) *
    Real.arctan ‖spinPlaneFlow (Real.exp s) z v‖) _ t
  apply h.congr_deriv
  rw [spinSphereFlow_speed, norm_mul]
  have he := Real.exp_ne_zero s
  have hd : 1 + ‖spinPlaneFlow (Real.exp s) z t‖ ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp

/-- Exact speed integral on every oriented real time interval. -/
theorem spinSphereFlow_integral_speed (s : ℝ) (z : ℂ) (u v : ℝ) :
    (∫ t in u..v, ‖spinSphereField (Real.exp s) (spinSphereFlow (Real.exp s) z t)‖) =
      spinRemainingLength s z u - spinRemainingLength s z v := by
  have hc := (continuous_spinSphereFlow_speed (Real.exp s) z).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_spinRemainingLength s z t) (hc.intervalIntegrable u v)
  simp only [intervalIntegral.integral_neg] at h
  linarith

/-- The remaining-length potential vanishes at infinite forward time. -/
theorem spinRemainingLength_tendsto_zero (s : ℝ) (z : ℂ) :
    Tendsto (spinRemainingLength s z) atTop (nhds 0) := by
  have hr := (spinPlaneFlow_positive_tendsto_zero s z).norm
  have ha := Real.continuous_arctan.continuousAt.tendsto.comp hr
  have h := ha.const_mul (2 * ‖spinPlaneRate (Real.exp s)‖ / (Real.exp s) ^ (2 : ℕ))
  unfold spinRemainingLength
  simpa only [Function.comp_apply, norm_zero, Real.arctan_zero, mul_zero] using h

/-- Exact finite total forward arclength of the damped precessing spin. -/
theorem spinSphereFlow_total_arclength (s : ℝ) (z : ℂ) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T,
      ‖spinSphereField (Real.exp s) (spinSphereFlow (Real.exp s) z t)‖) atTop
      (nhds ((2 * ‖spinPlaneRate (Real.exp s)‖ / (Real.exp s) ^ (2 : ℕ)) * Real.arctan ‖z‖)) := by
  have hc : Tendsto (fun _ : ℝ => spinRemainingLength s z 0) atTop
      (nhds (spinRemainingLength s z 0)) := tendsto_const_nhds
  have h := hc.sub (spinRemainingLength_tendsto_zero s z)
  simpa only [spinSphereFlow_integral_speed, spinRemainingLength, spinPlaneFlow_zero, sub_zero] using h

end
end GaloisForLFunctions.HTGeometry.SchafferExl
