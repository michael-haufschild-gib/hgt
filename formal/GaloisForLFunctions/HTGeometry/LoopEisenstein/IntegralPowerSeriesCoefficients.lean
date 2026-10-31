import GaloisForLFunctions.HTGeometry.PowerSeriesCoeffSubalgebra
import GaloisForLFunctions.HTGeometry.LoopEisenstein.ValuedSL2Iwasawa

/-!
# Coefficient-integral power-series matrices

The coefficient condition is a subring condition. Inversion of a principal
power-series unit stays in this subring by the coefficient recursion.
Constant reduction sends integral determinant-one matrices to integral
special-linear matrices over the coefficient field.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open Matrix
open scoped WithZero WithZeroMulInt
noncomputable section
variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

private def valuationIntegerAlgebra : Subalgebra ℤ F where
  toSubsemiring := v.integer.toSubsemiring
  algebraMap_mem' z := intCast_mem v.integer z

/-- Formal power series with every coefficient in the valuation integers. -/
def integralPowerSeriesCoefficients : Subring (PowerSeries F) :=
  (coeffSubalgebra (valuationIntegerAlgebra v)).toSubring

theorem mem_integralPowerSeriesCoefficients (f : PowerSeries F) :
    f ∈ integralPowerSeriesCoefficients v ↔ ∀ n, v (PowerSeries.coeff n f) ≤ 1 := Iff.rfl

/-- A principal unit and its inverse have the same coefficient-integrality property. -/
theorem invOfUnit_mem_integralPowerSeriesCoefficients {f : PowerSeries F}
    (hf : f ∈ integralPowerSeriesCoefficients v) (hf0 : PowerSeries.constantCoeff f = 1) :
    PowerSeries.invOfUnit f 1 ∈ integralPowerSeriesCoefficients v := by
  apply mem_coeffSubalgebra_of_mul_eq_one hf (PowerSeries.mul_invOfUnit f 1 hf0)
    (show (1 : F) ∈ valuationIntegerAlgebra v from (valuationIntegerAlgebra v).one_mem)
  rw [PowerSeries.coeff_zero_eq_constantCoeff, hf0, one_mul]

/-- Multiplication by the formal parameter shifts, but does not alter, coefficient integrality. -/
theorem X_mul_mem_integralPowerSeriesCoefficients_iff (f : PowerSeries F) :
    PowerSeries.X * f ∈ integralPowerSeriesCoefficients v ↔
      f ∈ integralPowerSeriesCoefficients v := by
  constructor
  · intro h n
    simpa only [PowerSeries.coeff_succ_X_mul] using h (n + 1)
  · intro h n
    cases n with
    | zero => rw [PowerSeries.coeff_zero_X_mul]; exact (valuationIntegerAlgebra v).zero_mem
    | succ n => simpa only [PowerSeries.coeff_succ_X_mul] using h n

/-- Determinant-one power-series matrices integral in every coefficient. -/
def valuationIntegralPowerSeriesSL2 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (PowerSeries F)) where
  carrier := {g | ∀ i j, g i j ∈ integralPowerSeriesCoefficients v}
  one_mem' := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  mul_mem' := by
    intro g h hg hh i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact (integralPowerSeriesCoefficients v).add_mem
      ((integralPowerSeriesCoefficients v).mul_mem (hg i 0) (hh 0 j))
      ((integralPowerSeriesCoefficients v).mul_mem (hg i 1) (hh 1 j))
  inv_mem' := by
    intro g hg i j
    change (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (PowerSeries F)).1 i j ∈
      integralPowerSeriesCoefficients v
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hg 1 1
    · exact (integralPowerSeriesCoefficients v).neg_mem (hg 0 1)
    · exact (integralPowerSeriesCoefficients v).neg_mem (hg 1 0)
    · exact hg 0 0

/-- Constant reduction preserves coefficient integrality. -/
theorem integralPowerSeriesSL2_constant_reduction
    (g : Matrix.SpecialLinearGroup (Fin 2) (PowerSeries F))
    (hg : g ∈ valuationIntegralPowerSeriesSL2 v) :
    Matrix.SpecialLinearGroup.map (PowerSeries.constantCoeff (R := F)) g ∈ valuationIntegralSL2 v := by
  intro i j
  change v (PowerSeries.constantCoeff (g i j)) ≤ 1
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
    (mem_integralPowerSeriesCoefficients v (g i j)).mp (hg i j) 0

/-- A triangular constant reduction has valuation-unit diagonal entries. -/
theorem integralPowerSeriesSL2_diagonal_values (g : Matrix.SpecialLinearGroup (Fin 2) (PowerSeries F))
    (hg : g ∈ valuationIntegralPowerSeriesSL2 v)
    (hz : PowerSeries.constantCoeff (g 0 1) = 0 ∨ PowerSeries.constantCoeff (g 1 0) = 0) :
    v (PowerSeries.constantCoeff (g 0 0)) = 1 ∧
      v (PowerSeries.constantCoeff (g 1 1)) = 1 := by
  have hd := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hd
  have hc := congrArg (PowerSeries.constantCoeff (R := F)) hd
  simp only [map_sub, map_mul, map_one] at hc
  have he : PowerSeries.constantCoeff (g 0 0) * PowerSeries.constantCoeff (g 1 1) = 1 := by
    rcases hz with hb | hl
    · simpa only [hb, zero_mul, sub_zero] using hc
    · simpa only [hl, mul_zero, sub_zero] using hc
  have ha : v (PowerSeries.constantCoeff (g 0 0)) ≤ 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      (mem_integralPowerSeriesCoefficients v (g 0 0)).mp (hg 0 0) 0
  have hb : v (PowerSeries.constantCoeff (g 1 1)) ≤ 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      (mem_integralPowerSeriesCoefficients v (g 1 1)).mp (hg 1 1) 0
  have hv : v (PowerSeries.constantCoeff (g 0 0)) * v (PowerSeries.constantCoeff (g 1 1)) = 1 := by
    rw [← map_mul, he, map_one]
  constructor
  · apply le_antisymm ha
    calc
      1 = v (PowerSeries.constantCoeff (g 0 0)) * v (PowerSeries.constantCoeff (g 1 1)) := hv.symm
      _ ≤ v (PowerSeries.constantCoeff (g 0 0)) * 1 := mul_le_mul_left' hb _
      _ = v (PowerSeries.constantCoeff (g 0 0)) := mul_one _
  · apply le_antisymm hb
    calc
      1 = v (PowerSeries.constantCoeff (g 0 0)) * v (PowerSeries.constantCoeff (g 1 1)) := hv.symm
      _ ≤ 1 * v (PowerSeries.constantCoeff (g 1 1)) := mul_le_mul_right' ha _
      _ = v (PowerSeries.constantCoeff (g 1 1)) := one_mul _

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.invOfUnit_mem_integralPowerSeriesCoefficients
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.integralPowerSeriesSL2_constant_reduction

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.integralPowerSeriesSL2_diagonal_values
