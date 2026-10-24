import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HeatConeEvolution
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.DivisorTransitions

/-!
# Dilation of polynomial heat

Dilation multiplies the heat parameter by the squared scale. Positive dilation preserves
every coefficient sign, so Gaussian root barriers transfer with their exact constants.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- Polynomial heat commutes with dilation after multiplying time by the squared scale. -/
theorem forwardPolyHeat_comp_dilation (s r : ℝ) (p : ℝ[X]) :
    forwardPolyHeat s (p.comp (C r * X)) =
      (forwardPolyHeat (s * r ^ 2) p).comp (C r * X) := by
  have hd (q : ℝ[X]) : derivative (q.comp (C r * X)) =
      C r * (derivative q).comp (C r * X) := by
    rw [derivative_comp]
    simp only [derivative_C_mul, derivative_X, mul_one]
  induction p using Polynomial.induction_on with
  | C c => simp only [C_comp, forwardPolyHeat_C]
  | add p q hp hq => simp only [add_comp, forwardPolyHeat_add, hp, hq]
  | monomial n c ih =>
    have he : C c * X ^ (n + 1) = X * (C c * X ^ n) := by ring
    simp only [he, mul_comp, X_comp]
    rw [mul_assoc, forwardPolyHeat_C_mul, forwardPolyHeat_X_mul, ih, hd,
      forwardPolyHeat_X_mul]
    simp only [add_comp, mul_comp, X_comp, C_comp, map_mul, map_pow, map_ofNat]
    ring

/-- Positive dilation changes the heat parameter but preserves every coefficient sign. -/
theorem coeffNonneg_heat_dilation_iff (s : ℝ) {r : ℝ} (hr : 0 < r) (p : ℝ[X]) :
    CoeffNonneg (forwardPolyHeat s (p.comp (C r * X))) ↔
      CoeffNonneg (forwardPolyHeat (s * r ^ 2) p) := by
  rw [forwardPolyHeat_comp_dilation, coeffNonneg_positive_rescale_iff _ hr]

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
