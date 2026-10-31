import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralPowerSeriesCoefficients
import GaloisForLFunctions.HTGeometry.LoopEisenstein.VertexParabolics

/-!
# Integral matrices at adjacent power-series vertices

When a diagonal shift remains a power-series matrix, it preserves
coefficient integrality. The two off-diagonal entries shift by one
coefficient in opposite directions; their zero boundary coefficients
are exactly the Iwahori conditions.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open Matrix
open scoped WithZero WithZeroMulInt
noncomputable section
variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

/-- Adjacent diagonal shifts preserve integral coefficients whenever both matrices are positive. -/
theorem integralPowerSeriesSL2_rescale_Xinv_iff (p q : PowerSeriesSL2 F)
    (he : powerSeriesSL2Map F q = sl2Rescale (laurentXUnit F)⁻¹ (powerSeriesSL2Map F p)) :
    q ∈ valuationIntegralPowerSeriesSL2 v ↔ p ∈ valuationIntegralPowerSeriesSL2 v := by
  have h00 : q 0 0 = p 0 0 := HahnSeries.ofPowerSeries_injective
    (congrArg (fun g : SL2 (LaurentSeries F) => g 0 0) he)
  have h11 : q 1 1 = p 1 1 := HahnSeries.ofPowerSeries_injective
    (congrArg (fun g : SL2 (LaurentSeries F) => g 1 1) he)
  have h01 : PowerSeries.X * q 0 1 = p 0 1 := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ))
    rw [PowerSeries.coe_mul, PowerSeries.coe_X]
    have hh := congrArg (fun g : SL2 (LaurentSeries F) => g 0 1) he
    change (q 0 1 : LaurentSeries F) =
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * (p 0 1 : LaurentSeries F) at hh
    rw [hh]
    change (laurentXUnit F : LaurentSeries F) *
      ((((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * (p 0 1 : LaurentSeries F)) = _
    rw [← mul_assoc]
    simp only [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  have h10 : q 1 0 = PowerSeries.X * p 1 0 := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ))
    rw [PowerSeries.coe_mul, PowerSeries.coe_X]
    have hh := congrArg (fun g : SL2 (LaurentSeries F) => g 1 0) he
    change (q 1 0 : LaurentSeries F) =
      (((((laurentXUnit F)⁻¹)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * (p 1 0 : LaurentSeries F)) at hh
    simpa only [inv_inv, coe_laurentXUnit] using hh
  constructor
  · intro h i j
    fin_cases i <;> fin_cases j
    · exact h00 ▸ h 0 0
    · exact h01 ▸ (X_mul_mem_integralPowerSeriesCoefficients_iff v (q 0 1)).mpr (h 0 1)
    · exact (X_mul_mem_integralPowerSeriesCoefficients_iff v (p 1 0)).mp (h10 ▸ h 1 0)
    · exact h11 ▸ h 1 1
  · intro h i j
    fin_cases i <;> fin_cases j
    · exact h00.symm ▸ h 0 0
    · apply (X_mul_mem_integralPowerSeriesCoefficients_iff v (q 0 1)).mp
      rw [h01]; exact h 0 1
    · exact h10.symm ▸ (X_mul_mem_integralPowerSeriesCoefficients_iff v (p 1 0)).mpr (h 1 0)
    · exact h11.symm ▸ h 1 1

/-- The inverse adjacent shift has the same coefficient-integrality equivalence. -/
theorem integralPowerSeriesSL2_rescale_X_iff (p q : PowerSeriesSL2 F)
    (he : powerSeriesSL2Map F q = sl2Rescale (laurentXUnit F) (powerSeriesSL2Map F p)) :
    q ∈ valuationIntegralPowerSeriesSL2 v ↔ p ∈ valuationIntegralPowerSeriesSL2 v := by
  have hi : powerSeriesSL2Map F p = sl2Rescale (laurentXUnit F)⁻¹ (powerSeriesSL2Map F q) := by
    rw [he, sl2Rescale_inverse]
  exact (integralPowerSeriesSL2_rescale_Xinv_iff v q p hi).symm

/-- Vanishing upper-right residue gives an actual integral Iwahori after the backward shift. -/
theorem exists_integralPowerSeries_affineShift (p : PowerSeriesSL2 F)
    (hp : p ∈ valuationIntegralPowerSeriesSL2 v)
    (hb : PowerSeries.constantCoeff (p 0 1) = 0) :
    ∃ q : PowerSeriesSL2 F, q ∈ valuationIntegralPowerSeriesSL2 v ∧
      q ∈ iwahoriMatrices F ∧
      powerSeriesSL2Map F q = sl2Rescale (laurentXUnit F)⁻¹ (powerSeriesSL2Map F p) := by
  obtain ⟨q, hq, he⟩ := affineShift_mem_laurentIwahori F p hb
  exact ⟨q, (integralPowerSeriesSL2_rescale_Xinv_iff v p q he).mpr hp, hq, he⟩

/-- An integral Iwahori matrix has an actual integral forward shift. -/
theorem exists_integralPowerSeries_forwardShift (p : PowerSeriesSL2 F)
    (hp : p ∈ valuationIntegralPowerSeriesSL2 v) (hi : p ∈ iwahoriMatrices F) :
    ∃ q : PowerSeriesSL2 F, q ∈ valuationIntegralPowerSeriesSL2 v ∧
      powerSeriesSL2Map F q = sl2Rescale (laurentXUnit F) (powerSeriesSL2Map F p) := by
  obtain ⟨q, he⟩ := laurentIwahori_le_affineVertex F
    (show powerSeriesSL2Map F p ∈ laurentIwahori F from ⟨p, hi, rfl⟩)
  exact ⟨q, (integralPowerSeriesSL2_rescale_X_iff v p q he).mpr hp, he⟩

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.integralPowerSeriesSL2_rescale_Xinv_iff
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_integralPowerSeries_affineShift
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_integralPowerSeries_forwardShift
