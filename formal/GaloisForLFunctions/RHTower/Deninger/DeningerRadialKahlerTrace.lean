import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# The radial Kähler lift and the two Meyer endpoint functionals

The radial lift `Rf(z) = f(|z|²)` carries an even Schwartz function to the complex leaf.  Its value
at the cone apex is `f(0)`, and its integral against the Kähler area is `π` times the integral of
`f` over the positive ray, because in polar coordinates the area is `ρ dρ dθ` and `ρ dρ = dx/2`.
For an even function the ray integral is half the total integral, which is the Fourier transform at
the origin in Meyer's convention.  So Meyer's two endpoint conditions are exactly restriction to
the apex and vanishing of the leafwise Kähler trace.

* `deningerPolarTrace` : the polar reduction of a radial integral.
* `deningerRadialLift_zero` : the apex value `(3)`.
* `deningerRadialKahler_trace` : the Kähler trace `(4)`.
* `deningerMeyerEndpoint_iff` : the identification `(5)` ↔ `(6)`.
-/

namespace RHTower

open MeasureTheory Set Real

section PolarTrace

/-- The angular measure of the polar target, complex valued. -/
theorem deningerAngularIntegral_complex :
    (∫ _θ in Ioo (-π) π, (1 : ℂ)) = 2 * (π : ℂ) := by
  rw [setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π - -π)]
  rw [Complex.real_smul]
  push_cast
  ring

/-- The radial integral in the squared radius coordinate, complex valued. -/
theorem deningerRadialSquareSubstitution_complex (F : ℝ → ℂ) :
    (∫ r in Ioi (0 : ℝ), (r : ℂ) * F (r ^ 2)) = (1 / 2 : ℂ) * ∫ x in Ioi (0 : ℝ), F x := by
  have h := integral_comp_rpow_Ioi (fun x => F x) (p := 2) (by norm_num)
  have hcongr : ∀ r ∈ Ioi (0 : ℝ),
      (|(2 : ℝ)| * r ^ ((2 : ℝ) - 1)) • F (r ^ (2 : ℝ)) = (2 : ℂ) * ((r : ℂ) * F (r ^ 2)) := by
    intro r hr
    have hx2 : r ^ (2 : ℝ) = r ^ 2 := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, hx2,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul]
    push_cast
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul] at h
  rw [← h]
  ring

/-- **The polar reduction of a radial integral.**  Integrating a function of the squared modulus
against the Kähler area is `π` times its integral over the positive ray. -/
theorem deningerPolarTrace (F : ℝ → ℂ) :
    (∫ z : ℂ, F (‖z‖ ^ 2)) = (π : ℂ) * ∫ x in Ioi (0 : ℝ), F x := by
  have hpolar := Complex.integral_comp_polarCoord_symm (fun z : ℂ => F (‖z‖ ^ 2))
  rw [← hpolar, polarCoord_target]
  have hcongr : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      p.1 • F (‖Complex.polarCoord.symm p‖ ^ 2)
        = ((p.1 : ℂ) * F (p.1 ^ 2)) * (1 : ℂ) := by
    rintro ⟨r, θ⟩ hp
    have hr : (0 : ℝ) < r := hp.1
    have habs : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    simp only [mul_one]
    rw [habs, Complex.real_smul]
  rw [MeasureTheory.setIntegral_congr_fun
      (measurableSet_Ioi.prod measurableSet_Ioo) hcongr,
    MeasureTheory.Measure.volume_eq_prod,
    show (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ((p.1 : ℂ) * F (p.1 ^ 2)) * (1 : ℂ)
          ∂(volume.prod volume))
        = (∫ r in Ioi (0 : ℝ), (r : ℂ) * F (r ^ 2)) * ∫ _θ in Ioo (-π) π, (1 : ℂ) from
      setIntegral_prod_mul (fun r : ℝ => (r : ℂ) * F (r ^ 2)) (fun _ : ℝ => (1 : ℂ))
        (Ioi (0 : ℝ)) (Ioo (-π) π),
    deningerAngularIntegral_complex, deningerRadialSquareSubstitution_complex]
  ring

end PolarTrace

section Endpoints

/-- The radial Kähler lift of an even function. -/
noncomputable def deningerRadialLift (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  f (‖z‖ ^ 2)

/-- **The apex value.**  The lift at the cone apex is the value at the origin. -/
theorem deningerRadialLift_zero (f : ℝ → ℂ) : deningerRadialLift f 0 = f 0 := by
  rw [deningerRadialLift]
  norm_num

/-- **The leafwise Kähler trace.**  The integral of the lift against the Kähler area is `π` times
the ray integral. -/
theorem deningerRadialKahler_trace (f : ℝ → ℂ) :
    (∫ z : ℂ, deningerRadialLift f z) = (π : ℂ) * ∫ x in Ioi (0 : ℝ), f x :=
  deningerPolarTrace f

/-- The total integral of an even integrable function is twice its ray integral. -/
theorem deningerEven_integral (f : ℝ → ℂ) (heven : ∀ x, f (-x) = f x) (hint : Integrable f) :
    (∫ x : ℝ, f x) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have hIic : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    have h := integral_comp_neg_Iic (0 : ℝ) f
    rw [neg_zero] at h
    rw [← h]
    exact (setIntegral_congr_fun measurableSet_Iic fun x _ => (heven x).symm)
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (f := f) (b := (0 : ℝ)) hint.integrableOn hint.integrableOn
  rw [hIic] at hsplit
  rw [← hsplit]
  ring

/-- Meyer's Fourier transform. -/
noncomputable def deningerMeyerFourier (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (2 * (π : ℂ) * Complex.I * (x : ℂ) * (y : ℂ))

theorem deningerMeyerFourier_zero (f : ℝ → ℂ) :
    deningerMeyerFourier f 0 = ∫ x : ℝ, f x := by
  rw [deningerMeyerFourier]
  simp

/-- **The Kähler trace is the Fourier transform at the origin**, up to the fixed normalization
`π/2`. -/
theorem deningerRadialKahler_trace_fourier (f : ℝ → ℂ) (heven : ∀ x, f (-x) = f x)
    (hint : Integrable f) :
    (∫ z : ℂ, deningerRadialLift f z) = ((π : ℂ) / 2) * deningerMeyerFourier f 0 := by
  rw [deningerRadialKahler_trace, deningerMeyerFourier_zero,
    deningerEven_integral f heven hint]
  ring

/-- **Meyer's endpoint conditions are apex restriction and Kähler trace.** -/
theorem deningerMeyerEndpoint_iff (f : ℝ → ℂ) (heven : ∀ x, f (-x) = f x)
    (hint : Integrable f) :
    (f 0 = 0 ∧ deningerMeyerFourier f 0 = 0)
      ↔ (deningerRadialLift f 0 = 0 ∧ (∫ z : ℂ, deningerRadialLift f z) = 0) := by
  rw [deningerRadialLift_zero, deningerRadialKahler_trace_fourier f heven hint]
  constructor
  · rintro ⟨h0, hF⟩
    exact ⟨h0, by rw [hF, mul_zero]⟩
  · rintro ⟨h0, hT⟩
    refine ⟨h0, ?_⟩
    have hpi : ((π : ℂ) / 2) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt Real.pi_pos
      exact div_ne_zero this two_ne_zero
    rcases mul_eq_zero.mp hT with h | h
    · exact absurd h hpi
    · exact h

/-- **Meyer's domain on even Schwartz functions.**  For an even Schwartz function the two endpoint
conditions are exactly apex restriction and vanishing Kähler trace of the radial lift. -/
theorem deningerMeyerEndpoint_schwartz (f : SchwartzMap ℝ ℂ) (heven : ∀ x, f (-x) = f x) :
    ((f : ℝ → ℂ) 0 = 0 ∧ deningerMeyerFourier (f : ℝ → ℂ) 0 = 0)
      ↔ (deningerRadialLift (f : ℝ → ℂ) 0 = 0
          ∧ (∫ z : ℂ, deningerRadialLift (f : ℝ → ℂ) z) = 0) :=
  deningerMeyerEndpoint_iff (f : ℝ → ℂ) heven (SchwartzMap.integrable f)

end Endpoints

end RHTower
