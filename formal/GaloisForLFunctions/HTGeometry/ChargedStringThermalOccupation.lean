import GaloisForLFunctions.HTGeometry.CPVRadiationTemperature

/-!
# Charged string horizons from the corpus thermal occupation

Equations (51)--(57) of arXiv:2608.21406v1 apply to the existing CPV coherent
radius and geometric occupation law. The squared charge parameter is the thermal
ratio. Hawking temperature is the vacuum occupation times `exp ell / (4*pi)`;
the reduced-state purity is an exact rational function of this temperature.
The metric derivative, exterior positivity, and all parameter bounds are proved.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

def stringBlackHoleLapse (ell tau x : ℝ) : ℝ :=
  (1 - Real.exp (-Real.exp ell * x)) *
    (1 - thermalRatio tau * Real.exp (-Real.exp ell * x))

def stringBlackHolePotential (ell tau x : ℝ) : ℝ :=
  coherentRadius tau * Real.exp (-Real.exp ell * x)

def stringBlackHoleTemperature (ell tau : ℝ) : ℝ :=
  Real.exp ell / (4 * Real.pi) * (1 - thermalRatio tau)

theorem stringBlackHoleLapse_derivative (ell tau x : ℝ) :
    HasDerivAt (stringBlackHoleLapse ell tau)
      (Real.exp ell * Real.exp (-Real.exp ell * x) *
        (1 + thermalRatio tau - 2 * thermalRatio tau * Real.exp (-Real.exp ell * x))) x := by
  have he := ((hasDerivAt_id x).const_mul (-Real.exp ell)).exp
  apply ((he.const_sub 1).mul ((he.const_mul (thermalRatio tau)).const_sub 1)).congr_deriv
  dsimp
  ring

theorem stringBlackHoleLapse_horizon (ell tau : ℝ) : stringBlackHoleLapse ell tau 0 = 0 := by
  simp [stringBlackHoleLapse]

theorem stringBlackHole_surfaceGravity (ell tau : ℝ) :
    deriv (stringBlackHoleLapse ell tau) 0 = 4 * Real.pi * stringBlackHoleTemperature ell tau := by
  rw [(stringBlackHoleLapse_derivative ell tau 0).deriv]
  simp only [mul_zero, Real.exp_zero, mul_one, stringBlackHoleTemperature]
  field_simp
  ring

theorem stringBlackHoleTemperature_pos (ell tau : ℝ) : 0 < stringBlackHoleTemperature ell tau := by
  unfold stringBlackHoleTemperature
  exact mul_pos (div_pos (Real.exp_pos ell) (by positivity)) (sub_pos.mpr (thermalRatio_lt_one tau))

theorem stringBlackHoleTemperature_vacuum (ell tau : ℝ) :
    stringBlackHoleTemperature ell tau = Real.exp ell / (4 * Real.pi) * radiationMass tau 0 := by
  simp [stringBlackHoleTemperature, radiationMass, canonicalThermalMass]

theorem stringBlackHole_charge_temperature (ell tau : ℝ) :
    coherentRadius tau ^ 2 + 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell = 1 := by
  rw [coherentRadius_sq, stringBlackHoleTemperature]
  field_simp
  ring

theorem stringBlackHole_charge_from_temperature (ell tau : ℝ) :
    coherentRadius tau = Real.sqrt (1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell) := by
  have h := stringBlackHole_charge_temperature ell tau
  rw [show 1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell =
    coherentRadius tau ^ 2 by linarith, Real.sqrt_sq_eq_abs, abs_of_pos (coherentRadius_pos tau)]

theorem stringBlackHole_thermal_purity (ell tau : ℝ) :
    (∑' n, radiationMass tau n ^ 2) =
      (4 * Real.pi * stringBlackHoleTemperature ell tau) /
        (2 * Real.exp ell - 4 * Real.pi * stringBlackHoleTemperature ell tau) := by
  rw [radiationMass_purity, stringBlackHoleTemperature]
  have h1 : 1 + thermalRatio tau ≠ 0 := by linarith [thermalRatio_pos tau]
  have h2 : 2 * Real.exp ell - 4 * Real.pi *
      (Real.exp ell / (4 * Real.pi) * (1 - thermalRatio tau)) =
      Real.exp ell * (1 + thermalRatio tau) := by field_simp; ring
  rw [h2]
  field_simp

theorem stringBlackHoleLapse_exterior_pos (ell tau x : ℝ) :
    0 < stringBlackHoleLapse ell tau (Real.exp x) := by
  have hz : 0 < Real.exp (-Real.exp ell * Real.exp x) := Real.exp_pos _
  have hz1 : Real.exp (-Real.exp ell * Real.exp x) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have h : 0 < Real.exp ell * Real.exp x := mul_pos (Real.exp_pos ell) (Real.exp_pos x)
    linarith
  unfold stringBlackHoleLapse
  apply mul_pos (sub_pos.mpr hz1)
  apply sub_pos.mpr
  calc thermalRatio tau * Real.exp (-Real.exp ell * Real.exp x) < thermalRatio tau * 1 :=
    mul_lt_mul_of_pos_left hz1 (thermalRatio_pos tau)
    _ < 1 := by simpa using thermalRatio_lt_one tau

theorem stringBlackHolePotential_exterior_bounds (ell tau x : ℝ) :
    0 < stringBlackHolePotential ell tau (Real.exp x) ∧
      stringBlackHolePotential ell tau (Real.exp x) < coherentRadius tau := by
  have hz1 : Real.exp (-Real.exp ell * Real.exp x) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have h : 0 < Real.exp ell * Real.exp x := mul_pos (Real.exp_pos ell) (Real.exp_pos x)
    linarith
  constructor
  · exact mul_pos (coherentRadius_pos tau) (Real.exp_pos _)
  · simpa [stringBlackHolePotential] using mul_lt_mul_of_pos_left hz1 (coherentRadius_pos tau)

end GaloisForLFunctions.HTGeometry.CPV
