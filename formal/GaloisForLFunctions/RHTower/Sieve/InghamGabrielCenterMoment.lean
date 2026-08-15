import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGaussianTranslatedMoment
import GaloisForLFunctions.RHTower.Sieve.InghamRightGaussianTranslatedMoment
import GaloisForLFunctions.RHTower.Sieve.InghamGabrielScalarAnalytic
import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielIntegralInterpolation

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

theorem continuous_poleCleared_vertical_of_half_le
    (X : ℕ) {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    Continuous fun t : ℝ =>
      inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hpoint0 : z + (t : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hpath : ContinuousAt (fun u : ℝ => z + (u : ℂ) * I) t := by fun_prop
  change ContinuousAt
    (inghamGabrielPoleClearedError X 1 (X : ℝ) ∘
      fun u : ℝ => z + (u : ℂ) * I) t
  exact ContinuousAt.comp_of_eq
    (analyticAt_inghamGabrielPoleClearedError X 1 (X : ℝ) hpoint0).continuousAt
    hpath rfl

/-- Exact fixed-Gabriel powered center-moment estimate for the actual pole-cleared field. -/
theorem exists_inghamGabrielPoleClearedError_centerMoment_powered_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      (inghamFixedGabrielCenterMoment
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ)) ^
          (11859 / 18200 : ℝ) ≤ C * (X : ℝ) ^ (259069 / 568750 : ℝ) := by
  obtain ⟨CL, hCL, hleft⟩ :=
    exists_inghamGabrielPoleClearedError_critical_translatedMoment_le
  obtain ⟨CR, hCR, hright⟩ :=
    exists_inghamGabrielPoleClearedError_powerSavingRight_translatedMoment_le
  let K : ℝ := (CL + 1) ^ (8277 / 18200 : ℝ) *
    (CR + 1) ^ (3582 / 18200 : ℝ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  let L : ℝ := (CL + 1) * (X : ℝ) ^ (251 / 250 : ℝ)
  let R : ℝ := (CR + 1) * (X : ℝ) ^ (-(1 / 180 : ℝ))
  have hL : 0 < L := by dsimp only [L]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hinterp :=
    inghamFixedGabrielCenterMoment_interpolate_of_vertical_continuous
      (fun z hz => continuous_poleCleared_vertical_of_half_le X hz)
      (X : ℝ) L R hL hR
      (diffContOnCl_inghamFixedGabrielScalarFamily_poleCleared X
        (kappa := 1) (T := (X : ℝ)) hXpos.le)
      (bddAbove_inghamFixedGabrielScalarFamily_poleCleared X
        (kappa := 1) (T := (X : ℝ)) (by norm_num) hXpos)
      (fun z hz => by
        have h := hleft hX z hz
        dsimp only [L]
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg hXpos.le _)))
      (fun z hz => by
        have h := hright hX z hz
        dsimp only [R]
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg hXpos.le _)))
  calc
    (inghamFixedGabrielCenterMoment
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ)) ^
          (11859 / 18200 : ℝ) ≤
            L ^ (8277 / 18200 : ℝ) * R ^ (3582 / 18200 : ℝ) := hinterp
    _ = K * (X : ℝ) ^ (259069 / 568750 : ℝ) := by
      dsimp only [L, R, K]
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hXpos.le _),
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hXpos.le _),
        ← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le]
      calc
        (CL + 1) ^ (8277 / 18200 : ℝ) *
              (X : ℝ) ^ ((251 / 250 : ℝ) * (8277 / 18200 : ℝ)) *
            ((CR + 1) ^ (3582 / 18200 : ℝ) *
              (X : ℝ) ^ (-(1 / 180 : ℝ) * (3582 / 18200 : ℝ))) =
            ((CL + 1) ^ (8277 / 18200 : ℝ) *
              (CR + 1) ^ (3582 / 18200 : ℝ)) *
              ((X : ℝ) ^ ((251 / 250 : ℝ) * (8277 / 18200 : ℝ)) *
                (X : ℝ) ^ (-(1 / 180 : ℝ) * (3582 / 18200 : ℝ))) := by ring
        _ = ((CL + 1) ^ (8277 / 18200 : ℝ) *
              (CR + 1) ^ (3582 / 18200 : ℝ)) *
              (X : ℝ) ^ (259069 / 568750 : ℝ) := by
            rw [← Real.rpow_add hXpos]
            congr 1
            norm_num

/-- Actual pole-cleared center moment has the exact Route T exponent, strictly below `7/10`. -/
theorem exists_inghamGabrielPoleClearedError_centerMoment_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      inghamFixedGabrielCenterMoment
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) ≤
          C * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := by
  obtain ⟨K, hK, hpowered⟩ :=
    exists_inghamGabrielPoleClearedError_centerMoment_powered_le
  let C : ℝ := K ^ (18200 / 11859 : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX
  let I0 : ℝ := inghamFixedGabrielCenterMoment
    (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ)
  have hI0 : 0 ≤ I0 := inghamFixedGabrielCenterMoment_nonneg _ _
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _)
    (hpowered hX) (by norm_num : (0 : ℝ) ≤ 18200 / 11859)
  calc
    I0 = (I0 ^ (11859 / 18200 : ℝ)) ^ (18200 / 11859 : ℝ) := by
      rw [← Real.rpow_mul hI0]
      norm_num
    _ ≤ (K * (X : ℝ) ^ (259069 / 568750 : ℝ)) ^
          (18200 / 11859 : ℝ) := hpow
    _ = C * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := by
      dsimp only [C]
      rw [Real.mul_rpow hK (Real.rpow_nonneg hXpos.le _),
        ← Real.rpow_mul hXpos.le, inghamFixedGabrielRouteTExponent_eq]
      congr 2
      norm_num

end

end RHTower.Sieve
