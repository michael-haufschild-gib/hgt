import GaloisForLFunctions.HTGeometry.PolynomialHeatProduct
import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatTimeSpreadsTheConfiguration

/-!
# Composition of the polynomial heat clock

The multiplication-by-`X` identity and commutation with differentiation
prove the semigroup law by polynomial induction. Nonreal-root contraction
then compares arbitrary heat times. Mapping real coefficients into complex
polynomials identifies this clock with the complex zero-velocity flow.
-/

open Polynomial Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics

/-- Composing forward polynomial heat adds its parameters. -/
theorem forwardPolyHeat_comp (s t : ℝ) (p : ℝ[X]) :
    forwardPolyHeat s (forwardPolyHeat t p) = forwardPolyHeat (s + t) p := by
  have hpow (n : ℕ) : forwardPolyHeat s (forwardPolyHeat t (X ^ n)) =
      forwardPolyHeat (s + t) (X ^ n) := by
    induction n with
    | zero => simp only [pow_zero, ← Polynomial.C_1, forwardPolyHeat_C]
    | succ n ih =>
      have hd : forwardPolyHeat s (derivative (forwardPolyHeat t (X ^ n))) =
          derivative (forwardPolyHeat (s + t) (X ^ n)) := by
        rw [← derivative_forwardPolyHeat, ih]
      simp only [pow_succ', forwardPolyHeat_X_mul, forwardPolyHeat_add,
        forwardPolyHeat_C_mul]
      rw [ih, hd]
      rw [show C (2 * (s + t)) = C (2 * s) + C (2 * t) by rw [mul_add, map_add]]
      ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [forwardPolyHeat_add, hp, hq]
  | monomial n a =>
    simp only [← C_mul_X_pow_eq_monomial, forwardPolyHeat_C_mul, hpow]

/-- Composing backward polynomial heat adds its parameters. -/
theorem polyHeat_comp (s t : ℝ) (p : ℝ[X]) :
    polyHeat s (polyHeat t p) = polyHeat (s + t) p := by
  simpa only [forwardPolyHeat_eq_polyHeat, neg_neg, neg_add] using
    forwardPolyHeat_comp (-s) (-t) p

/-- The full nonreal multiplicity count decreases across arbitrary real heat times. -/
theorem antitone_nonrealRootCount_polyHeat {p : ℝ[X]} (hp : p ≠ 0) :
    Antitone (fun t : ℝ => nonrealRootCount (polyHeat t p)) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · exact le_rfl
  have h := nonrealRootCount_polyHeat_le (sub_pos.mpr hab) (natDegree_polyHeat a hp).2
  rwa [polyHeat_comp, sub_add_cancel] at h

#print axioms forwardPolyHeat_comp
#print axioms polyHeat_comp
#print axioms antitone_nonrealRootCount_polyHeat

/-- The real and complex polynomial backward-heat definitions agree. -/
theorem heatFlow_ofReal (t : ℝ) (p : ℝ[X]) :
    heatFlow (t : ℂ) (p.map Complex.ofRealHom) = (polyHeat t p).map Complex.ofRealHom := by
  rw [heatFlow, natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  simp only [polyHeat, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    iterate_derivative_map]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  congr 1
  change (-(t : ℂ)) ^ k / (k.factorial : ℂ) = (((-t) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
  push_cast
  rfl

/-- Constant perturbations commute with polynomial heat. -/
theorem polyHeat_add_constant (t c : ℝ) (p : ℝ[X]) :
    polyHeat t (p + C c) = polyHeat t p + C c := by
  have h := forwardPolyHeat_add (-t) p (C c)
  rw [forwardPolyHeat_C] at h
  simpa only [forwardPolyHeat_eq_polyHeat, neg_neg] using h

#print axioms heatFlow_ofReal
#print axioms polyHeat_add_constant

end GaloisForLFunctions.ArithmeticElectrostatics

