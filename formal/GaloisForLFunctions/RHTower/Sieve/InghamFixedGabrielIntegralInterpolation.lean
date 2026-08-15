import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielScalarFamily

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Fixed Gabriel interpolation for the concrete dual scalar integral. The only remaining inputs are
strip regularity/boundedness and uniform translated endpoint moments. -/
theorem inghamFixedGabrielCenterMoment_interpolate
    {f : ℂ → ℂ} (hf : Continuous f) (T L R : ℝ)
    (hL : 0 < L) (hR : 0 < R)
    (hd : DiffContOnCl ℂ (inghamFixedGabrielScalarFamily f T)
      (Complex.HadamardThreeLines.verticalStrip (1 / 2) inghamPowerSavingRightEdge))
    (hB : BddAbove ((norm ∘ inghamFixedGabrielScalarFamily f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) inghamPowerSavingRightEdge))
    (hleftMoment : ∀ z : ℂ, z.re = 1 / 2 →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤ L)
    (hrightMoment : ∀ z : ℂ, z.re = inghamPowerSavingRightEdge →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤ R) :
    (inghamFixedGabrielCenterMoment f T) ^ (237 / 364 : ℝ) ≤
      L ^ (165 / 364 : ℝ) * R ^ (72 / 364 : ℝ) := by
  by_cases hIzero : inghamFixedGabrielCenterMoment f T = 0
  · rw [hIzero, Real.zero_rpow (by norm_num : (237 / 364 : ℝ) ≠ 0)]
    positivity
  · have hI : 0 < inghamFixedGabrielCenterMoment f T :=
      lt_of_le_of_ne (inghamFixedGabrielCenterMoment_nonneg f T) (Ne.symm hIzero)
    apply inghamFixedGabriel_of_scalarFamily hL hR hI hd hB
    · intro z hz
      have hzre : z.re = 1 / 2 := by simpa using hz
      have hhold := norm_inghamFixedGabrielScalarFamily_left_le hf T hzre
      have hm0 : 0 ≤ ∫ t in Icc (-T) T,
          ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) :=
        integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
      have hpow :
          (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
              (3 / 4 : ℝ) ≤ L ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hm0 (hleftMoment z hzre) (by norm_num)
      exact hhold.trans (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (inghamFixedGabrielCenterMoment_nonneg f T) _))
    · intro z hz
      have hzre : z.re = inghamPowerSavingRightEdge := by simpa using hz
      have hhold := norm_inghamFixedGabrielScalarFamily_right_le hf T hzre
      have hm0 : 0 ≤ ∫ t in Icc (-T) T,
          ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ) :=
        integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
      have hpow :
          (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^
              (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hm0 (hrightMoment z hzre) (by norm_num)
      exact hhold.trans (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (inghamFixedGabrielCenterMoment_nonneg f T) _))
    · exact norm_inghamFixedGabrielScalarFamily_center f T

end

end RHTower.Sieve

