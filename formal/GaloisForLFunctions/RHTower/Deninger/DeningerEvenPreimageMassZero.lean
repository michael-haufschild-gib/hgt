import GaloisForLFunctions.RHTower.Deninger.DeningerPreimageL1
import GaloisForLFunctions.RHTower.Deninger.DeningerPreimageZeroMass

/-!
# The even extension has zero mass on the line

Reflection carries the negative ray onto the positive one, so the even extension has the same mass
on each half; the ray mass is zero, hence so is the total.

This is the whole content of the two endpoint conditions of Meyer's space: the value of a Fourier
transform at the origin *is* the total mass of its argument, so `(12)` supplies both endpoints of
the kernel theorem with no Poisson summation.

* `deningerEvenPreimage_integral_zero` : **`∫_ℝ E f_h = 0`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- **The even extension of the canonical preimage has zero total mass.** -/
theorem deningerEvenPreimage_integral_zero {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    (∫ x : ℝ, deningerEvenPreimage h x) = 0 := by
  have hint : Integrable (deningerEvenPreimage h) := deningerEvenPreimage_integrable hh
  have hpos : IntegrableOn (deningerEvenPreimage h) (Set.Ioi 0) := hint.integrableOn
  have hneg : IntegrableOn (deningerEvenPreimage h) (Set.Iic 0) := hint.integrableOn
  have hsplit : (∫ x in Set.Iic (0 : ℝ), deningerEvenPreimage h x)
      + ∫ x in Set.Ioi (0 : ℝ), deningerEvenPreimage h x
      = ∫ x : ℝ, deningerEvenPreimage h x :=
    intervalIntegral.integral_Iic_add_Ioi hneg hpos
  have hrefl : (∫ x in Set.Ioi (0 : ℝ), deningerEvenPreimage h (-x))
      = ∫ x in Set.Iic (0 : ℝ), deningerEvenPreimage h x := by
    have := integral_comp_neg_Ioi (0 : ℝ) (deningerEvenPreimage h)
    rwa [neg_zero] at this
  have heven : (∫ x in Set.Ioi (0 : ℝ), deningerEvenPreimage h (-x))
      = ∫ x in Set.Ioi (0 : ℝ), deningerEvenPreimage h x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    exact deningerEvenPreimage_even h x
  have hray : (∫ x in Set.Ioi (0 : ℝ), deningerEvenPreimage h x) = 0 := by
    rw [← deningerMobiusPreimage_mass_eq_zero hh]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    exact deningerEvenPreimage_of_pos h hx
  rw [← hsplit, ← hrefl, heven, hray, add_zero]

end

end RHTower
