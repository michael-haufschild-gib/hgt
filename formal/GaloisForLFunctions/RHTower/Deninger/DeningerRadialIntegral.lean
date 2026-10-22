import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# The radial integral on a complex leaf

Integrating a radial function over a complex leaf against the Kähler form is, after polar
coordinates and the substitution `s = r²`, integration against `ds` on the positive half-line,
with the single factor `π`.

This identifies the radial Hilbert measure of the half-density leaf with `L²(ℝ_{>0}, ds)`.

* `deningerComplex_integral_norm` : the polar-coordinate form.
* `deningerRadial_sq_substitution` : the substitution `s = r²`.
* `deningerRadial_integral_eq` : the identification, `∫_ℂ g(|z|²) = π ∫_0^∞ g`.
-/

namespace RHTower

open MeasureTheory

section RadialIntegral

/-- The unit ball of the complex line has area `π`. -/
theorem deningerComplex_volume_real_unitBall :
    MeasureTheory.volume.real (Metric.ball (0 : ℂ) 1) = Real.pi := by
  rw [MeasureTheory.measureReal_def, Complex.volume_ball]
  simp

/-- **The polar-coordinate form of a radial integral.** -/
theorem deningerComplex_integral_norm (g : ℝ → ℝ) :
    ∫ z : ℂ, g ‖z‖ = 2 * Real.pi * ∫ y in Set.Ioi (0 : ℝ), y * g y := by
  rw [MeasureTheory.integral_fun_norm_addHaar volume g, Complex.finrank_real_complex,
    deningerComplex_volume_real_unitBall]
  have hpt : ∀ y : ℝ, y ^ (2 - 1) • g y = y * g y := by
    intro y
    norm_num
  simp only [hpt, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The substitution `s = r²`.** -/
theorem deningerRadial_sq_substitution (g : ℝ → ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), y * g (y ^ 2) = (1 / 2) * ∫ s in Set.Ioi (0 : ℝ), g s := by
  have h := MeasureTheory.integral_comp_rpow_Ioi g (p := 2) (by norm_num)
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ),
      (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ)) = 2 * (x * g (x ^ 2)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : x ^ ((2 : ℝ) - 1) = x := by
      norm_num
    have h2 : x ^ (2 : ℝ) = x ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h1, h2, smul_eq_mul]
    norm_num
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt] at h
  rw [MeasureTheory.integral_const_mul] at h
  rw [← h]
  ring

/-- **The radial integral on a complex leaf.**  Integrating a radial function against the Kähler
form is `π` times its integral on the positive half-line. -/
theorem deningerRadial_integral_eq (g : ℝ → ℝ) :
    ∫ z : ℂ, g (‖z‖ ^ 2) = Real.pi * ∫ s in Set.Ioi (0 : ℝ), g s := by
  have h := deningerComplex_integral_norm (fun y => g (y ^ 2))
  rw [h, deningerRadial_sq_substitution g]
  ring

end RadialIntegral

end RHTower
