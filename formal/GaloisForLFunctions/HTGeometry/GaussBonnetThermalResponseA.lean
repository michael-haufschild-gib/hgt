import GaloisForLFunctions.HTGeometry.GaussBonnetGibbsAGauge

/-!
# Actual radial thermal response for logarithmic Gauss–Bonnet entropy

Differentiate the model-A temperature itself. Define isobaric heat capacity
as T times the actual entropy derivative divided by the actual temperature
derivative, so later stability statements concern thermodynamic functions
rather than a separately postulated sign polynomial.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbTemperatureARadialSlope (P Q a r : ℝ) : ℝ :=
  (8 * Real.pi * P * r ^ (6 : ℕ) + 48 * Real.pi * P * a ^ (2 : ℕ) * r ^ (4 : ℕ) - r ^ (4 : ℕ) +
    (2 * a ^ (2 : ℕ) + 3 * (Q ^ (2 : ℕ) + a ^ (2 : ℕ))) * r ^ (2 : ℕ) + 2 * a ^ (2 : ℕ) * (Q ^ (2 : ℕ) + a ^ (2 : ℕ))) /
  (4 * Real.pi * r ^ (2 : ℕ) * (r ^ (2 : ℕ) + 2 * a ^ (2 : ℕ)) ^ (2 : ℕ))

def egbHeatCapacityA (P Q a l r : ℝ) : ℝ :=
  egbTemperatureA P Q a r * deriv (egbEntropyA a l) r / deriv (egbTemperatureA P Q a) r

theorem egbTemperatureA_hasDerivAt (P Q a x : ℝ) :
    HasDerivAt (egbTemperatureA P Q a) (egbTemperatureARadialSlope P Q a (exp x)) (exp x) := by
  have hN := (((((hasDerivAt_id (exp x)).pow 4).const_mul (8 * Real.pi * P)).add
    ((hasDerivAt_id (exp x)).pow 2)).sub_const (Q ^ (2 : ℕ))).sub_const (a ^ (2 : ℕ))
  have hD := ((hasDerivAt_id (exp x)).const_mul (4 * Real.pi)).mul
    (((hasDerivAt_id (exp x)).pow 2).add_const (2 * a ^ (2 : ℕ)))
  have h := hN.div hD (by change 4 * Real.pi * exp x * (exp x ^ (2 : ℕ) + 2 * a ^ (2 : ℕ)) ≠ 0; positivity)
  apply h.congr_deriv
  unfold egbTemperatureARadialSlope
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, id_eq, Nat.cast_ofNat]
  field_simp
  ring

theorem egbHeatCapacityA_formula (P Q a l x : ℝ) :
    egbHeatCapacityA P Q a l (exp x) = egbTemperatureA P Q a (exp x) *
      (2 * Real.pi * exp x + 4 * Real.pi * a ^ (2 : ℕ) / exp x) / egbTemperatureARadialSlope P Q a (exp x) := by
  unfold egbHeatCapacityA
  rw [(egbEntropyA_derivative a l x).deriv, (egbTemperatureA_hasDerivAt P Q a x).deriv]

/-- The entropy reference length cannot change the actual isobaric heat capacity. -/
theorem egbHeatCapacityA_reference_invariant (P Q a l₁ l₂ x : ℝ) :
    egbHeatCapacityA P Q a l₁ (exp x) = egbHeatCapacityA P Q a l₂ (exp x) := by
  rw [egbHeatCapacityA_formula, egbHeatCapacityA_formula]

/-- Equation (10) of arXiv:2609.00025, derived from the actual entropy and temperature. -/
theorem egbHeatCapacityA_paper_formula (P Q a l x : ℝ) :
    egbHeatCapacityA P Q a l (exp x) =
    2 * Real.pi * (exp x ^ (2 : ℕ) + 2 * a ^ (2 : ℕ)) ^ (2 : ℕ) * (8 * Real.pi * P * exp x ^ (4 : ℕ) + exp x ^ (2 : ℕ) - Q ^ (2 : ℕ) - a ^ (2 : ℕ)) /
      (8 * Real.pi * P * exp x ^ (6 : ℕ) + 48 * Real.pi * P * a ^ (2 : ℕ) * exp x ^ (4 : ℕ) - exp x ^ (4 : ℕ) +
        (3 * Q ^ (2 : ℕ) + 5 * a ^ (2 : ℕ)) * exp x ^ (2 : ℕ) + 2 * a ^ (2 : ℕ) * (Q ^ (2 : ℕ) + a ^ (2 : ℕ))) := by
  rw [egbHeatCapacityA_formula]
  unfold egbTemperatureARadialSlope
  rw [div_div_eq_mul_div]
  have hd : 2 * a ^ (2 : ℕ) + 3 * (Q ^ (2 : ℕ) + a ^ (2 : ℕ)) = 3 * Q ^ (2 : ℕ) + 5 * a ^ (2 : ℕ) := by ring
  rw [hd]
  congr 1
  unfold egbTemperatureA
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
