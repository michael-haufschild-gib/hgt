import GaloisForLFunctions.HTGeometry.LoopEisenstein.PowerSeriesRowCorrection

/-!
# Kubota coordinates of positive loops

Right upper-root multiplication preserves the Kubota coordinate. On positive
loops the coordinate is the embedded lower-left entry, unless that entry
vanishes, in which case it is the embedded lower-right entry.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {K : Type*} [Field K]

theorem kubotaUnit_mul_upper (g : SL2 K) (s : K) :
    kubotaUnit (g * sl2Upper s) = kubotaUnit g := by
  classical
  have hc : (g * sl2Upper s) 1 0 = g 1 0 := by
    simp [sl2Upper, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hd : (g * sl2Upper s) 1 1 = g 1 0 * s + g 1 1 := by
    simp [sl2Upper, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  apply Units.ext
  change (if (g * sl2Upper s) 1 0 = 0 then (g * sl2Upper s) 1 1 else
      (g * sl2Upper s) 1 0) = if g 1 0 = 0 then g 1 1 else g 1 0
  simp only [hc, hd]
  by_cases h : g 1 0 = 0
  · simp only [h, zero_mul, zero_add]
  · simp only [if_neg h]

/-- An arbitrary matrix has no cocycle defect against a right upper-root element. -/
theorem kubotaCocycle_mul_upper (g : SL2 K) (s : K) :
    kubotaCocycle g (sl2Upper s) = 0 := by
  simp only [kubotaCocycle, kubotaUnit_mul_upper, kubotaUnit_upper,
    div_eq_mul_inv, mul_inv_cancel, inv_one, mul_one, milnorSym2_one_left]

variable (F : Type*) [Field F]

theorem kubotaUnit_powerSeries_of_left_ne_zero (g : PowerSeriesSL2 F) (hc : g 1 0 ≠ 0) :
    kubotaUnit (powerSeriesSL2Map F g) = powerSeriesFieldUnit F (g 1 0) hc := by
  classical
  apply Units.ext
  rw [coe_kubotaUnit, coe_powerSeriesFieldUnit]
  change (if (HahnSeries.ofPowerSeries ℤ F) (g 1 0) = 0 then
      (HahnSeries.ofPowerSeries ℤ F) (g 1 1) else
      (HahnSeries.ofPowerSeries ℤ F) (g 1 0)) = _
  exact if_neg (powerSeriesFieldUnit F (g 1 0) hc).ne_zero

theorem kubotaUnit_powerSeries_of_left_zero (g : PowerSeriesSL2 F)
    (hc : g 1 0 = 0) (hd : g 1 1 ≠ 0) :
    kubotaUnit (powerSeriesSL2Map F g) = powerSeriesFieldUnit F (g 1 1) hd := by
  classical
  apply Units.ext
  rw [coe_kubotaUnit, coe_powerSeriesFieldUnit]
  change (if (HahnSeries.ofPowerSeries ℤ F) (g 1 0) = 0 then
      (HahnSeries.ofPowerSeries ℤ F) (g 1 1) else
      (HahnSeries.ofPowerSeries ℤ F) (g 1 0)) = _
  rw [hc, map_zero, if_pos rfl]

theorem kubotaUnit_powerSeries_lower (s : PowerSeries F) (hs : s ≠ 0) :
    kubotaUnit (sl2Lower (s : LaurentSeries F)) = powerSeriesFieldUnit F s hs :=
  kubotaUnit_lower_unit (powerSeriesFieldUnit F s hs)

/-- The tame factor multiplying the central coordinates of two positive loops. -/
def powerSeriesKubotaFactor (g h : PowerSeriesSL2 F) : Fˣ :=
  laurentTameSymbol F
    (kubotaUnit (powerSeriesSL2Map F (g * h)) / kubotaUnit (powerSeriesSL2Map F g))
    (kubotaUnit (powerSeriesSL2Map F (g * h)) / kubotaUnit (powerSeriesSL2Map F h))

theorem powerSeriesKubotaFactor_eq (g h : PowerSeriesSL2 F) :
    Additive.ofMul (powerSeriesKubotaFactor F g h) =
      laurentTameHom F (kubotaCocycle (powerSeriesSL2Map F g) (powerSeriesSL2Map F h)) := by
  rw [kubotaCocycle, laurentTameHom_symbol, powerSeriesKubotaFactor, map_mul]

@[simp] theorem powerSeriesKubotaFactor_one_right (g : PowerSeriesSL2 F) :
    powerSeriesKubotaFactor F g 1 = 1 := by
  apply Additive.ofMul.injective
  rw [powerSeriesKubotaFactor_eq, map_one, kubotaCocycle_one_right, map_zero]
  rfl

@[simp] theorem powerSeriesKubotaFactor_upper (g : PowerSeriesSL2 F) (s : PowerSeries F) :
    powerSeriesKubotaFactor F g (FiniteRingSl2.upper s) = 1 := by
  apply Additive.ofMul.injective
  rw [powerSeriesKubotaFactor_eq, powerSeriesSL2Map_upper, kubotaCocycle_mul_upper, map_zero]
  rfl

private theorem factor_lower_nonzero (g : PowerSeriesSL2 F) (s : PowerSeries F)
    (hc : g 1 0 ≠ 0) (hs : s ≠ 0) (he : g 1 0 + g 1 1 * s ≠ 0) :
    powerSeriesKubotaFactor F g (FiniteRingSl2.lower s) =
      laurentTameSymbol F
        (powerSeriesFieldUnit F (g 1 0 + g 1 1 * s) he / powerSeriesFieldUnit F (g 1 0) hc)
        (powerSeriesFieldUnit F (g 1 0 + g 1 1 * s) he / powerSeriesFieldUnit F s hs) := by
  have he' : (g * FiniteRingSl2.lower s) 1 0 ≠ 0 := by
    simpa only [powerSeriesSL2_mul_lower_c] using he
  have hx := kubotaUnit_powerSeries_of_left_ne_zero F (g * FiniteRingSl2.lower s) he'
  simp only [powerSeriesSL2_mul_lower_c] at hx
  rw [powerSeriesKubotaFactor, hx, kubotaUnit_powerSeries_of_left_ne_zero F g hc,
    powerSeriesSL2Map_lower, kubotaUnit_powerSeries_lower F s hs]

private theorem factor_lower_left_zero (g : PowerSeriesSL2 F) (s : PowerSeries F)
    (hc : g 1 0 = 0) (hd : g 1 1 ≠ 0) (hs : s ≠ 0) (he : g 1 0 + g 1 1 * s ≠ 0) :
    powerSeriesKubotaFactor F g (FiniteRingSl2.lower s) =
      laurentTameSymbol F
        (powerSeriesFieldUnit F (g 1 0 + g 1 1 * s) he / powerSeriesFieldUnit F (g 1 1) hd)
        (powerSeriesFieldUnit F (g 1 0 + g 1 1 * s) he / powerSeriesFieldUnit F s hs) := by
  have he' : (g * FiniteRingSl2.lower s) 1 0 ≠ 0 := by
    simpa only [powerSeriesSL2_mul_lower_c] using he
  have hx := kubotaUnit_powerSeries_of_left_ne_zero F (g * FiniteRingSl2.lower s) he'
  simp only [powerSeriesSL2_mul_lower_c] at hx
  rw [powerSeriesKubotaFactor, hx, kubotaUnit_powerSeries_of_left_zero F g hc hd,
    powerSeriesSL2Map_lower, kubotaUnit_powerSeries_lower F s hs]

private theorem factor_lower_sum_zero (g : PowerSeriesSL2 F) (s : PowerSeries F)
    (hc : g 1 0 ≠ 0) (hd : g 1 1 ≠ 0) (hs : s ≠ 0) (he : g 1 0 + g 1 1 * s = 0) :
    powerSeriesKubotaFactor F g (FiniteRingSl2.lower s) =
      laurentTameSymbol F
        (powerSeriesFieldUnit F (g 1 1) hd / powerSeriesFieldUnit F (g 1 0) hc)
        (powerSeriesFieldUnit F (g 1 1) hd / powerSeriesFieldUnit F s hs) := by
  have he' : (g * FiniteRingSl2.lower s) 1 0 = 0 := by
    simpa only [powerSeriesSL2_mul_lower_c] using he
  have hd' : (g * FiniteRingSl2.lower s) 1 1 ≠ 0 := by
    simpa only [powerSeriesSL2_mul_lower_d] using hd
  have hx := kubotaUnit_powerSeries_of_left_zero F (g * FiniteRingSl2.lower s) he' hd'
  simp only [powerSeriesSL2_mul_lower_d] at hx
  rw [powerSeriesKubotaFactor, hx, kubotaUnit_powerSeries_of_left_ne_zero F g hc,
    powerSeriesSL2Map_lower, kubotaUnit_powerSeries_lower F s hs]

private theorem correction_lower_unit (g : PowerSeriesSL2 F) (s : PowerSeries F)
    (hd₀ : PowerSeries.constantCoeff (g 1 1) ≠ 0) :
    powerSeriesRowCorrection F (g 1 0 + g 1 1 * s) (g 1 1) =
      powerSeriesRowCorrection F (g 1 0) (g 1 1) *
        powerSeriesKubotaFactor F g (FiniteRingSl2.lower s) := by
  by_cases hs : s = 0
  · rw [hs, mul_zero, add_zero, FiniteRingSl2.lower_zero,
      powerSeriesKubotaFactor_one_right, mul_one]
  have hd := powerSeries_ne_zero_of_constant F (g 1 1) hd₀
  have hdd : laurentTameSymbol F (powerSeriesFieldUnit F (g 1 1) hd)
      (powerSeriesFieldUnit F (g 1 1) hd) = 1 := by
    simp only [powerSeriesFieldUnit_eq_laurentUnit F (g 1 1) hd hd₀]
    exact laurentTameSymbol_powerSeriesUnits F _ _
  by_cases hc : g 1 0 = 0
  · have he : g 1 0 + g 1 1 * s ≠ 0 := by
      rw [hc, zero_add]
      exact mul_ne_zero hd hs
    have hu : powerSeriesFieldUnit F (g 1 0 + g 1 1 * s) he =
        powerSeriesFieldUnit F (g 1 1) hd * powerSeriesFieldUnit F s hs := by
      apply Units.ext
      simp only [coe_powerSeriesFieldUnit, Units.val_mul]
      change (HahnSeries.ofPowerSeries ℤ F) (g 1 0 + g 1 1 * s) = _
      rw [hc, zero_add, map_mul]
    rw [powerSeriesRowCorrection_of_right_unit F _ _ he hd₀,
      factor_lower_left_zero F g s hc hd hs he, hu, hc, powerSeriesRowCorrection_zero, one_mul]
    exact laurentTameSymbol_initial_shear F _ _ hdd
  by_cases he : g 1 0 + g 1 1 * s = 0
  · have hu : powerSeriesFieldUnit F (g 1 0) hc =
        -powerSeriesFieldUnit F (g 1 1) hd * powerSeriesFieldUnit F s hs := by
      apply Units.ext
      simp only [coe_powerSeriesFieldUnit, Units.val_mul, Units.val_neg]
      have hg : g 1 0 = -(g 1 1) * s := by linear_combination he
      change (HahnSeries.ofPowerSeries ℤ F) (g 1 0) = _
      rw [hg, map_mul, map_neg]
    rw [he, powerSeriesRowCorrection_zero,
      powerSeriesRowCorrection_of_right_unit F _ _ hc hd₀,
      factor_lower_sum_zero F g s hc hd hs he, hu]
    exact (laurentTameSymbol_zero_shear F _ _ hdd).symm
  · rw [powerSeriesRowCorrection_of_right_unit F _ _ he hd₀,
      powerSeriesRowCorrection_of_right_unit F _ _ hc hd₀,
      factor_lower_nonzero F g s hc hs he]
    have hsum : (powerSeriesFieldUnit F (g 1 0 + g 1 1 * s) he : LaurentSeries F) =
        (powerSeriesFieldUnit F (g 1 0) hc : LaurentSeries F) +
          (powerSeriesFieldUnit F (g 1 1) hd : LaurentSeries F) * powerSeriesFieldUnit F s hs := by
      simp only [coe_powerSeriesFieldUnit]
      exact (map_add (HahnSeries.ofPowerSeries ℤ F) _ _).trans
        (congrArg (fun u => (HahnSeries.ofPowerSeries ℤ F) (g 1 0) + u)
          (map_mul (HahnSeries.ofPowerSeries ℤ F) _ _))
    rw [laurentTameSymbol_lower_shear F _ _ _ _ hsum]
    rw [mul_left_comm, mul_inv_cancel, mul_one]

/-- The correction absorbs the entire lower-root Kubota factor. -/
theorem powerSeriesRowCorrection_lower (g : PowerSeriesSL2 F) (s : PowerSeries F) :
    powerSeriesRowCorrection F (g 1 0 + g 1 1 * s) (g 1 1) =
      powerSeriesRowCorrection F (g 1 0) (g 1 1) *
        powerSeriesKubotaFactor F g (FiniteRingSl2.lower s) := by
  by_cases hd₀ : PowerSeries.constantCoeff (g 1 1) = 0
  · have hc₀ := (powerSeriesSL2_bottom_constants F g).resolve_right (not_not.mpr hd₀)
    have he₀ : PowerSeries.constantCoeff (g 1 0 + g 1 1 * s) ≠ 0 := by
      simpa only [map_add, map_mul, hd₀, zero_mul, add_zero] using hc₀
    rw [powerSeriesRowCorrection_of_right_nonunit F _ _ hd₀,
      powerSeriesRowCorrection_of_right_nonunit F _ _ hd₀, one_mul]
    by_cases hs : s = 0
    · rw [hs, FiniteRingSl2.lower_zero, powerSeriesKubotaFactor_one_right]
    · rw [factor_lower_nonzero F g s (powerSeries_ne_zero_of_constant F _ hc₀) hs
        (powerSeries_ne_zero_of_constant F _ he₀)]
      symm
      apply laurentTameSymbol_ratio_of_equal_constants F (g 1 0) (g 1 0 + g 1 1 * s) hc₀ he₀
      simp only [map_add, map_mul, hd₀, zero_mul, add_zero]
  · exact correction_lower_unit F g s hd₀

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
