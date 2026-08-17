import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Exact quadratic divisor-front factor

This module records the exact formal-series input at the first nontrivial local layer of the
divisor-front calculation. It deliberately stops before the analytic logarithm and all
Riemann-hypothesis-dependent material.

The correction is
`X² (1 - X) / (1 - X²)`. The denominator is represented by its geometric power series, so every
result below is an unconditional identity in `ℚ⟦X⟧`.
-/

open PowerSeries

namespace GaloisForLFunctions.RHTower

/-- The formal geometric inverse of `1 - X²`. -/
noncomputable def quadraticLayerEvenGeom : ℚ⟦X⟧ :=
  (PowerSeries.invUnitsSub (1 : ℚˣ)).subst (X ^ 2)

/-- The exact local correction `X² (1-X)/(1-X²)`. -/
noncomputable def quadraticLayerCorrection : ℚ⟦X⟧ :=
  X ^ 2 * (1 - X) * quadraticLayerEvenGeom

/-- The geometric denominator is exact. -/
theorem quadraticLayerEvenGeom_mul_denominator :
    quadraticLayerEvenGeom * (1 - X ^ 2) = 1 := by
  have hX : PowerSeries.HasSubst (X ^ 2 : ℚ⟦X⟧) :=
    PowerSeries.HasSubst.X_pow (by norm_num)
  have hinv : PowerSeries.invUnitsSub (1 : ℚˣ) * (1 - X) = 1 := by
    simpa using PowerSeries.invUnitsSub_mul_sub (1 : ℚˣ)
  have h := congrArg (PowerSeries.subst (X ^ 2 : ℚ⟦X⟧)) hinv
  rw [PowerSeries.subst_mul hX, PowerSeries.subst_sub hX,
    PowerSeries.subst_X hX] at h
  have hone : (1 : ℚ⟦X⟧).subst (X ^ 2 : ℚ⟦X⟧) = 1 := by
    simpa only [PowerSeries.coe_substAlgHom] using
      (map_one (PowerSeries.substAlgHom hX))
  rw [hone] at h
  simpa [quadraticLayerEvenGeom] using h

/-- The formal quotient has its exact denominator-free numerator identity. -/
theorem quadraticLayerFrontFactor :
    (1 - X ^ 2) * (1 + quadraticLayerCorrection) = 1 - X ^ 3 := by
  have hgeom : (1 - X ^ 2) * quadraticLayerEvenGeom = 1 := by
    rw [mul_comm]
    exact quadraticLayerEvenGeom_mul_denominator
  rw [quadraticLayerCorrection]
  calc
    (1 - X ^ 2) * (1 + X ^ 2 * (1 - X) * quadraticLayerEvenGeom)
        = (1 - X ^ 2) + X ^ 2 * (1 - X) * ((1 - X ^ 2) * quadraticLayerEvenGeom) := by
            ring
    _ = (1 - X ^ 2) + X ^ 2 * (1 - X) := by rw [hgeom, mul_one]
    _ = 1 - X ^ 3 := by ring

/-- The first nonzero coefficient of the quadratic correction. -/
theorem quadraticLayerCorrection_coeff_two :
    PowerSeries.coeff 2 quadraticLayerCorrection = 1 := by
  rw [quadraticLayerCorrection, mul_assoc, PowerSeries.coeff_X_pow_mul']
  norm_num [quadraticLayerEvenGeom, PowerSeries.coeff_mul]

/-- The next coefficient is the linear finite-geometric correction. -/
theorem quadraticLayerCorrection_coeff_three :
    PowerSeries.coeff 3 quadraticLayerCorrection = -1 := by
  rw [quadraticLayerCorrection, mul_assoc, PowerSeries.coeff_X_pow_mul']
  rw [PowerSeries.coeff_one_mul]
  norm_num [quadraticLayerEvenGeom, PowerSeries.coeff_X]

/-- The first repeated geometric coefficient appears at degree four. -/
theorem quadraticLayerCorrection_coeff_four :
    PowerSeries.coeff 4 quadraticLayerCorrection = 1 := by
  rw [quadraticLayerCorrection, mul_assoc, PowerSeries.coeff_X_pow_mul']
  rw [PowerSeries.coeff_mul]
  have h : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by rfl
  rw [h]
  norm_num [quadraticLayerEvenGeom, PowerSeries.coeff_X]

/-- Exact initial jet of the first intrinsic divisor-front correction. -/
theorem quadraticLayerCorrection_initial_jet :
    PowerSeries.coeff 2 quadraticLayerCorrection = 1 ∧
      PowerSeries.coeff 3 quadraticLayerCorrection = -1 ∧
        PowerSeries.coeff 4 quadraticLayerCorrection = 1 :=
  ⟨quadraticLayerCorrection_coeff_two, quadraticLayerCorrection_coeff_three,
    quadraticLayerCorrection_coeff_four⟩

end GaloisForLFunctions.RHTower
