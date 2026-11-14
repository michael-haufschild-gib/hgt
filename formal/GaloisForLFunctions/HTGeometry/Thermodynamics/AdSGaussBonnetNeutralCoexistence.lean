import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetCoexistence

/-!
# The neutral small--large line is hidden by thermal AdS

The zero-charge edge of the exact two-black-hole coexistence surface has
strictly positive free energy. Thermal AdS therefore dominates this edge,
even though its two black-hole radii are global minima among black holes.
The free-energy excess is exactly `k(1-k)²/(2(k²+4k+1)²)`.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

theorem coexistence_neutral_radius_sq (τ : ℝ) :
    coexistenceRadius τ 0 ^ 2 = 1 / coexistenceJ (CPV.thermalRatio τ) := by
  rw [coexistenceRadius_sq]
  simp [coexistenceSquare]

theorem coexistence_neutral_coupling (τ : ℝ) :
    coexistenceCoupling τ 0 = CPV.thermalRatio τ / (6 * coexistenceJ (CPV.thermalRatio τ)) := by
  have hp := coexistence_polynomials_pos τ
  have hJ := hp.2.2.1
  have hK := hp.2.2.2
  have hd : 3 * coexistenceK (CPV.thermalRatio τ) + coexistenceJ (CPV.thermalRatio τ) ≠ 0 := by positivity
  unfold coexistenceCoupling
  rw [coexistence_neutral_radius_sq]
  field_simp [hJ.ne', hd]
  unfold coexistenceN coexistenceD coexistenceJ coexistenceK
  ring

theorem coexistence_neutral_product_balance (τ : ℝ) :
    coexistenceProduct τ 0 - 6 * coexistenceCoupling τ 0 = 0 := by
  unfold coexistenceProduct
  rw [coexistence_neutral_radius_sq, coexistence_neutral_coupling]
  ring

theorem coexistence_neutral_constant (τ : ℝ) : coexistenceConstant τ 0 = 0 := by
  unfold coexistenceConstant
  rw [coexistence_neutral_product_balance, mul_zero, zero_div]

theorem coexistence_neutral_linear (τ : ℝ) : coexistenceLinear τ 0 = 0 := by
  unfold coexistenceLinear
  rw [coexistence_neutral_product_balance, mul_zero, zero_div]

theorem coexistence_neutral_charge (τ : ℝ) : coexistenceCharge τ 0 = 0 := by
  unfold coexistenceCharge
  rw [coexistence_neutral_constant, mul_zero, Real.sqrt_zero]

/-- The exact positive gap explains why neutral black-hole coexistence is not the dominant transition. -/
theorem coexistence_neutral_minimum (τ : ℝ) :
    coexistenceMinimum τ 0 =
      CPV.thermalRatio τ * (1 - CPV.thermalRatio τ) ^ 2 /
        (2 * coexistenceJ (CPV.thermalRatio τ) ^ 2) := by
  unfold coexistenceMinimum
  rw [coexistence_neutral_constant, coexistence_neutral_linear]
  simp only [zero_mul, mul_zero, sub_zero, zero_add]
  unfold coexistenceProduct
  rw [coexistence_neutral_radius_sq, coexistence_neutral_coupling]
  field_simp [(coexistence_polynomials_pos τ).2.2.1.ne']
  unfold coexistenceJ
  ring

theorem coexistence_neutral_minimum_pos (τ : ℝ) : 0 < coexistenceMinimum τ 0 := by
  rw [coexistence_neutral_minimum]
  have hk := CPV.thermalRatio_pos τ
  have hsplit := sub_pos.mpr (CPV.thermalRatio_lt_one τ)
  have hJ := (coexistence_polynomials_pos τ).2.2.1
  positivity

/-- Every neutral black hole lies above the zero free energy of thermal AdS at this coexistence temperature. -/
theorem neutral_coexistence_thermalAdS_dominates (τ u : ℝ) :
    0 < potential (coexistenceTemperature τ 0) 0 (coexistenceCoupling τ 0) 0 (Real.exp u) := by
  have h := (coexistence_neutral_minimum_pos τ).trans_le (coexistence_global_lower_bound τ 0 u)
  simpa only [coexistence_neutral_charge] using h

#print axioms coexistence_neutral_charge
#print axioms coexistence_neutral_minimum
#print axioms neutral_coexistence_thermalAdS_dominates

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
