import GaloisForLFunctions.HTGeometry.LoopEisenstein.PowerSeriesSL2

/-!
# The tame correction on integral bottom rows

For a unimodular power-series row `(c,d)`, the correction is `T(c,d)` when
`c` is nonzero and `d` is a unit, and one otherwise. Upper elementary
multiplication preserves this correction. The lower multiplication law is
controlled by a Steinberg identity for the shear `c ↦ c+ds`.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- A nonzero power series, regarded as a unit of the Laurent field. -/
def powerSeriesFieldUnit (p : PowerSeries F) (hp : p ≠ 0) : (LaurentSeries F)ˣ :=
  Units.mk0 (HahnSeries.ofPowerSeries ℤ F p) (by
    intro hz
    exact hp (HahnSeries.ofPowerSeries_injective
      (hz.trans (map_zero (HahnSeries.ofPowerSeries ℤ F)).symm)))

@[simp] theorem coe_powerSeriesFieldUnit (p : PowerSeries F) (hp : p ≠ 0) :
    (powerSeriesFieldUnit F p hp : LaurentSeries F) = (p : LaurentSeries F) := rfl

theorem powerSeries_ne_zero_of_constant (p : PowerSeries F)
    (hp : PowerSeries.constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h
  apply hp
  rw [h, map_zero]

/-- A power series with nonzero constant coefficient, as a power-series unit. -/
def powerSeriesUnitOfConstant (p : PowerSeries F)
    (hp : PowerSeries.constantCoeff p ≠ 0) : (PowerSeries F)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (Units.mk0 _ hp).isUnit).unit

@[simp] theorem coe_powerSeriesUnitOfConstant (p : PowerSeries F)
    (hp : PowerSeries.constantCoeff p ≠ 0) :
    (powerSeriesUnitOfConstant F p hp : PowerSeries F) = p :=
  IsUnit.unit_spec _

theorem powerSeriesFieldUnit_eq_laurentUnit (p : PowerSeries F) (hp : p ≠ 0)
    (hp₀ : PowerSeries.constantCoeff p ≠ 0) :
    powerSeriesFieldUnit F p hp =
      powerSeriesLaurentUnit F (powerSeriesUnitOfConstant F p hp₀) := by
  apply Units.ext
  rw [coe_powerSeriesFieldUnit, coe_powerSeriesLaurentUnit, coe_powerSeriesUnitOfConstant]

/-- The multiplicative central coordinate of the positive-loop section. -/
def powerSeriesRowCorrection (c d : PowerSeries F) : Fˣ := by
  classical
  exact if hc : c = 0 then 1 else
    if hd : PowerSeries.constantCoeff d = 0 then 1 else
      laurentTameSymbol F (powerSeriesFieldUnit F c hc)
        (powerSeriesFieldUnit F d (powerSeries_ne_zero_of_constant F d hd))

@[simp] theorem powerSeriesRowCorrection_zero (d : PowerSeries F) :
    powerSeriesRowCorrection F 0 d = 1 := by
  unfold powerSeriesRowCorrection
  exact dif_pos rfl

theorem powerSeriesRowCorrection_of_right_nonunit (c d : PowerSeries F)
    (hd : PowerSeries.constantCoeff d = 0) : powerSeriesRowCorrection F c d = 1 := by
  by_cases hc : c = 0
  · rw [hc, powerSeriesRowCorrection_zero]
  · simp only [powerSeriesRowCorrection, dif_neg hc, dif_pos hd]

theorem powerSeriesRowCorrection_of_right_unit (c d : PowerSeries F) (hc : c ≠ 0)
    (hd : PowerSeries.constantCoeff d ≠ 0) :
    powerSeriesRowCorrection F c d =
      laurentTameSymbol F (powerSeriesFieldUnit F c hc)
        (powerSeriesFieldUnit F d (powerSeries_ne_zero_of_constant F d hd)) := by
  simp only [powerSeriesRowCorrection, dif_neg hc, dif_neg hd]

@[simp] theorem powerSeriesRowCorrection_one_right (c : PowerSeries F) :
    powerSeriesRowCorrection F c 1 = 1 := by
  by_cases hc : c = 0
  · rw [hc, powerSeriesRowCorrection_zero]
  · have h₁ : PowerSeries.constantCoeff (1 : PowerSeries F) ≠ 0 := by
      rw [map_one]
      exact one_ne_zero
    rw [powerSeriesRowCorrection_of_right_unit F c 1 hc h₁]
    have hu : powerSeriesFieldUnit F 1 (powerSeries_ne_zero_of_constant F 1 h₁) = 1 := by
      apply Units.ext
      exact map_one (HahnSeries.ofPowerSeries ℤ F)
    rw [hu, laurentTameSymbol_one_right]

/-- A unit left entry makes the correction trivial, including the second Bruhat chart. -/
theorem powerSeriesRowCorrection_of_left_unit (c d : PowerSeries F)
    (hc : PowerSeries.constantCoeff c ≠ 0) : powerSeriesRowCorrection F c d = 1 := by
  by_cases hd : PowerSeries.constantCoeff d = 0
  · exact powerSeriesRowCorrection_of_right_nonunit F c d hd
  · rw [powerSeriesRowCorrection_of_right_unit F c d
      (powerSeries_ne_zero_of_constant F c hc) hd,
      powerSeriesFieldUnit_eq_laurentUnit F c _ hc,
      powerSeriesFieldUnit_eq_laurentUnit F d _ hd,
      laurentTameSymbol_powerSeriesUnits]

/-- Upper elementary multiplication preserves the correction on every unimodular row. -/
theorem powerSeriesRowCorrection_upper (c d s : PowerSeries F)
    (hrow : PowerSeries.constantCoeff c ≠ 0 ∨ PowerSeries.constantCoeff d ≠ 0) :
    powerSeriesRowCorrection F c (c * s + d) = powerSeriesRowCorrection F c d := by
  by_cases hc₀ : PowerSeries.constantCoeff c = 0
  · have hd := hrow.resolve_left (not_not.mpr hc₀)
    have he : PowerSeries.constantCoeff (c * s + d) ≠ 0 := by
      simpa only [map_add, map_mul, hc₀, zero_mul, zero_add] using hd
    by_cases hc : c = 0
    · rw [hc, powerSeriesRowCorrection_zero, powerSeriesRowCorrection_zero]
    · rw [powerSeriesRowCorrection_of_right_unit F c _ hc he,
        powerSeriesRowCorrection_of_right_unit F c d hc hd,
        powerSeriesFieldUnit_eq_laurentUnit F (c * s + d) _ he,
        powerSeriesFieldUnit_eq_laurentUnit F d _ hd]
      apply laurentTameSymbol_eq_of_residue_eq
      apply Units.ext
      simp only [coe_powerSeriesResidueUnit, coe_powerSeriesUnitOfConstant,
        map_add, map_mul, hc₀, zero_mul, zero_add]
  · rw [powerSeriesRowCorrection_of_left_unit F c _ hc₀,
      powerSeriesRowCorrection_of_left_unit F c d hc₀]

/-- A quotient of two units with equal constant coefficient is a principal unit. -/
theorem laurentTameSymbol_ratio_of_equal_constants (c e : PowerSeries F)
    (hc : PowerSeries.constantCoeff c ≠ 0) (he : PowerSeries.constantCoeff e ≠ 0)
    (hce : PowerSeries.constantCoeff c = PowerSeries.constantCoeff e)
    (a : (LaurentSeries F)ˣ) :
    laurentTameSymbol F
      (powerSeriesFieldUnit F e (powerSeries_ne_zero_of_constant F e he) /
        powerSeriesFieldUnit F c (powerSeries_ne_zero_of_constant F c hc)) a = 1 := by
  rw [powerSeriesFieldUnit_eq_laurentUnit F e _ he,
    powerSeriesFieldUnit_eq_laurentUnit F c _ hc, ← map_div]
  apply laurentTameSymbol_principalUnit_left
  have hr : powerSeriesResidueUnit F (powerSeriesUnitOfConstant F e he) =
      powerSeriesResidueUnit F (powerSeriesUnitOfConstant F c hc) := by
    apply Units.ext
    simpa only [coe_powerSeriesResidueUnit, coe_powerSeriesUnitOfConstant] using hce.symm
  rw [map_div, hr, div_eq_mul_inv, mul_inv_cancel]

/-- The nondegenerate lower shear is exactly the Steinberg relation. -/
theorem laurentTameSymbol_lower_shear
    (c d s e : (LaurentSeries F)ˣ)
    (he : (e : LaurentSeries F) = (c : LaurentSeries F) + (d : LaurentSeries F) * s) :
    laurentTameSymbol F (e / c) (e / s) =
      laurentTameSymbol F e d * (laurentTameSymbol F c d)⁻¹ := by
  have hsum : ((c / e : (LaurentSeries F)ˣ) : LaurentSeries F) +
      ((d * s / e : (LaurentSeries F)ˣ) : LaurentSeries F) = 1 := by
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    rw [← add_div, ← he, div_self e.ne_zero]
  have hst := laurentTameSymbol_add_eq_one F (c / e) (d * s / e) hsum
  have hinv : laurentTameSymbol F ((c / e)⁻¹) ((d * s / e)⁻¹) = 1 := by
    rw [laurentTameSymbol_inv_left, laurentTameSymbol_inv_right, hst, inv_one, inv_one]
  calc
    laurentTameSymbol F (e / c) (e / s) =
        laurentTameSymbol F ((c / e)⁻¹) (d * (d * s / e)⁻¹) := by
      congr 1
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      calc
        e * s⁻¹ = (e * s⁻¹) * (d * d⁻¹) := by rw [mul_inv_cancel, mul_one]
        _ = d * (e * (s⁻¹ * d⁻¹)) := by ac_rfl
    _ = laurentTameSymbol F ((c / e)⁻¹) d := by
      rw [laurentTameSymbol_mul_right, hinv, mul_one]
    _ = laurentTameSymbol F e d * (laurentTameSymbol F c d)⁻¹ := by
      rw [show (c / e)⁻¹ = e * c⁻¹ by simp [div_eq_mul_inv],
        laurentTameSymbol_mul_left, laurentTameSymbol_inv_left]

/-- The shear starting at a zero left entry uses only the diagonal-unit symbol. -/
theorem laurentTameSymbol_initial_shear (d s : (LaurentSeries F)ˣ)
    (hdd : laurentTameSymbol F d d = 1) :
    laurentTameSymbol F (d * s) d =
      laurentTameSymbol F ((d * s) / d) ((d * s) / s) := by
  rw [laurentTameSymbol_mul_left, hdd, one_mul]
  congr 1 <;> simp [div_eq_mul_inv]

/-- The shear ending at a zero left entry uses the opposite-pair symbol. -/
theorem laurentTameSymbol_zero_shear (d s : (LaurentSeries F)ˣ)
    (hdd : laurentTameSymbol F d d = 1) :
    laurentTameSymbol F (-d * s) d *
      laurentTameSymbol F (d / (-d * s)) (d / s) = 1 := by
  have hneg : laurentTameSymbol F ((-s)⁻¹) s⁻¹ = 1 := by
    rw [laurentTameSymbol_inv_left, laurentTameSymbol_inv_right, inv_inv]
    simpa only [neg_neg] using laurentTameSymbol_neg_self F (-s)
  rw [show -d * s = d * (-s) by simp only [neg_mul, mul_neg],
    laurentTameSymbol_mul_left, hdd, one_mul,
    show d / (d * (-s)) = (-s)⁻¹ by simp [div_eq_mul_inv, mul_comm],
    show d / s = d * s⁻¹ from div_eq_mul_inv d s,
    laurentTameSymbol_mul_right, hneg, mul_one,
    laurentTameSymbol_inv_left, mul_inv_cancel]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
