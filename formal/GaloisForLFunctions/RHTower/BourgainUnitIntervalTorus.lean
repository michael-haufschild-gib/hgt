/-
# Unit-circle averages as unit-interval Fourier integrals

Bourgain writes periodic mean values as integrals over `[0,1]`, whereas the
finite Parseval layer in this corpus uses `Real.circleAverage`.  This file
proves the exact change of variables between the two conventions.
-/
import Mathlib.MeasureTheory.Integral.CircleAverage

namespace RHTower

noncomputable section

/-- Standard unit-period additive character `e(x) = exp(2πix)`. -/
def bourgainUnitCharacter (x : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

@[simp] theorem norm_bourgainUnitCharacter (x : ℝ) :
    ‖bourgainUnitCharacter x‖ = 1 := by
  rw [bourgainUnitCharacter, Complex.norm_exp]
  simp

/-- A normalized unit-circle average is exactly the corresponding integral
over one real period. -/
theorem circleAverage_zero_one_eq_unitInterval (f : ℂ → ℝ) :
    Real.circleAverage f 0 1 =
      ∫ x in (0 : ℝ)..1, f (bourgainUnitCharacter x) := by
  rw [Real.circleAverage_eq_intervalAverage, interval_average_eq]
  simp only [sub_zero]
  have hchange :=
    intervalIntegral.integral_comp_mul_left
      (fun θ : ℝ => f (circleMap 0 1 θ))
      (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one] at hchange
  rw [← hchange]
  congr 1
  funext x
  simp only [circleMap_zero, bourgainUnitCharacter]
  congr 1
  push_cast
  ring_nf

/-- Iterating the one-dimensional identity gives the normalized two-torus
integral in Bourgain's `[0,1]²` convention. -/
theorem circleAverage_circleAverage_zero_one_eq_unitSquare
    (f : ℂ → ℂ → ℝ) :
    Real.circleAverage
        (fun v => Real.circleAverage (fun u => f u v) 0 1)
        0 1 =
      ∫ x₂ in (0 : ℝ)..1,
        ∫ x₁ in (0 : ℝ)..1,
          f (bourgainUnitCharacter x₁) (bourgainUnitCharacter x₂) := by
  rw [circleAverage_zero_one_eq_unitInterval]
  apply intervalIntegral.integral_congr
  intro x₂ _
  exact circleAverage_zero_one_eq_unitInterval
    (fun u => f u (bourgainUnitCharacter x₂))

end

end RHTower
