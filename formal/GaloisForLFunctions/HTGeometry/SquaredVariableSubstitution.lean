import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The squared-variable substitution

An even function of the spectral variable is a function of `u = x²`, and the substitution turns the
Lebesgue measure of the line into the half-line measure with the square-root density:

`∫_ℝ Φ(x²) dx = ∫_{u > 0} Φ(u) / √u du`.

This is the passage between the Fourier-side description of an even state and its squared-variable
description; the density `1/√u` is the Jacobian that carries all the analytic weight.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The image of the positive half-line under squaring. -/
theorem image_sq_Ioi_zero : (fun x : ℝ => x ^ 2) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact pow_pos hx 2
  · intro hu
    refine ⟨Real.sqrt u, Real.sqrt_pos.2 hu, ?_⟩
    rw [Real.sq_sqrt (le_of_lt hu)]

theorem injOn_sq_Ioi_zero : InjOn (fun x : ℝ => x ^ 2) (Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  nlinarith [hxy]

/-- **The squared-variable substitution on the half-line.** -/
theorem integral_Ioi_comp_sq (g : ℝ → ℝ) :
    (∫ u in Ioi (0 : ℝ), g u) = ∫ x in Ioi (0 : ℝ), (2 * x) * g (x ^ 2) := by
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := fun x : ℝ => x ^ 2) (f' := fun x : ℝ => 2 * x)
    measurableSet_Ioi
    (fun x _ => by
      have h : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x ^ 1) x := by
        simpa using (hasDerivAt_pow 2 x)
      simpa using h.hasDerivWithinAt)
    injOn_sq_Ioi_zero g
  rw [image_sq_Ioi_zero] at hchange
  rw [hchange]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  rw [smul_eq_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * x)]

/-- The half-line form of the substitution with the square-root density. -/
theorem integral_Ioi_sq_density (Φ : ℝ → ℝ) :
    (∫ u in Ioi (0 : ℝ), Φ u / (2 * Real.sqrt u)) = ∫ x in Ioi (0 : ℝ), Φ (x ^ 2) := by
  rw [integral_Ioi_comp_sq (fun u => Φ u / (2 * Real.sqrt u))]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hsqrt : Real.sqrt (x ^ 2) = x := by
    rw [Real.sqrt_sq hx0.le]
  rw [hsqrt]
  field_simp

/-! ## The full line -/

theorem integral_Iio_zero_comp_sq (Φ : ℝ → ℝ) :
    (∫ x in Iio (0 : ℝ), Φ (x ^ 2)) = ∫ x in Ioi (0 : ℝ), Φ (x ^ 2) := by
  have h := MeasureTheory.integral_comp_neg_Iio (a := (0 : ℝ)) (fun x : ℝ => Φ (x ^ 2))
  rw [neg_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Iio fun x _ => ?_
  rw [neg_pow, neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1) |>.2 (by decide), one_mul]

/-- **The squared-variable substitution on the line.**  An even state integrates against the
square-root density of the half-line. -/
theorem integral_comp_sq_eq_integral_Ioi (Φ : ℝ → ℝ) :
    (∫ x : ℝ, Φ (x ^ 2)) = ∫ u in Ioi (0 : ℝ), Φ u / Real.sqrt u := by
  have hsplit : (∫ x : ℝ, Φ (x ^ 2))
      = (∫ x in Iio (0 : ℝ), Φ (x ^ 2)) + ∫ x in Ioi (0 : ℝ), Φ (x ^ 2) := by
    rw [← integral_Iio_add_Ioi_eq_integral_univ, setIntegral_univ]
  rw [hsplit, integral_Iio_zero_comp_sq, ← two_mul, ← integral_Ioi_sq_density,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  have hs : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  field_simp

end GaloisForLFunctions.HTGeometry

end
