import GaloisForLFunctions.RHTower.Sieve.InghamGabrielCenterMoment
import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGaussianTranslatedMomentPolylog

open Complex MeasureTheory Set

namespace RHTower.Sieve

/-! # Fixed-Gabriel center moment with retained polylogarithmic loss -/

noncomputable section

theorem exists_inghamGabrielPoleClearedError_centerMoment_powered_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      (inghamFixedGabrielCenterMoment
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ)) ^
          (11859 / 18200 : ℝ) ≤
        C * (X : ℝ) ^ (82571 / 182000 : ℝ) *
          (1 + Real.log (X : ℝ)) ^ (8277 / 9100 : ℝ) := by
  obtain ⟨CL, hCL, hleft⟩ :=
    exists_inghamGabrielPoleClearedError_critical_translatedMoment_le_polylog
  obtain ⟨CR, hCR, hright⟩ :=
    exists_inghamGabrielPoleClearedError_powerSavingRight_translatedMoment_le
  let K : ℝ := (CL + 1) ^ (8277 / 18200 : ℝ) *
    (CR + 1) ^ (3582 / 18200 : ℝ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  let Log : ℝ := 1 + Real.log (X : ℝ)
  have hLog1 : 1 ≤ Log := by
    dsimp only [Log]
    linarith [Real.log_nonneg hXone]
  have hLog0 : 0 ≤ Log := by positivity
  let Left : ℝ := (CL + 1) * (X : ℝ) * Log ^ 2
  let Right : ℝ := (CR + 1) * (X : ℝ) ^ (-(1 / 180 : ℝ))
  have hLeft : 0 < Left := by dsimp only [Left]; positivity
  have hRight : 0 < Right := by dsimp only [Right]; positivity
  have hinterp :=
    inghamFixedGabrielCenterMoment_interpolate_of_vertical_continuous
      (fun z hz => continuous_poleCleared_vertical_of_half_le X hz)
      (X : ℝ) Left Right hLeft hRight
      (diffContOnCl_inghamFixedGabrielScalarFamily_poleCleared X
        (kappa := 1) (T := (X : ℝ)) hXpos.le)
      (bddAbove_inghamFixedGabrielScalarFamily_poleCleared X
        (kappa := 1) (T := (X : ℝ)) (by norm_num) hXpos)
      (fun z hz => by
        have h := hleft hX z hz
        dsimp only [Left, Log]
        exact h.trans (by
          gcongr
          linarith))
      (fun z hz => by
        have h := hright hX z hz
        dsimp only [Right]
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg hXpos.le _)))
  calc
    (inghamFixedGabrielCenterMoment
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ)) ^
          (11859 / 18200 : ℝ) ≤
        Left ^ (8277 / 18200 : ℝ) * Right ^ (3582 / 18200 : ℝ) := hinterp
    _ = K * (X : ℝ) ^ (82571 / 182000 : ℝ) *
        Log ^ (8277 / 9100 : ℝ) := by
      dsimp only [Left, Right, K]
      rw [Real.mul_rpow (mul_nonneg (by positivity) hXpos.le) (pow_nonneg hLog0 2),
        Real.mul_rpow (by positivity) hXpos.le,
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hXpos.le _),
        ← Real.rpow_natCast Log 2, ← Real.rpow_mul hLog0,
        ← Real.rpow_mul hXpos.le]
      calc
        ((CL + 1) ^ (8277 / 18200 : ℝ) *
              (X : ℝ) ^ (8277 / 18200 : ℝ) *
              Log ^ ((2 : ℝ) * (8277 / 18200 : ℝ))) *
            ((CR + 1) ^ (3582 / 18200 : ℝ) *
              (X : ℝ) ^ (-(1 / 180 : ℝ) * (3582 / 18200 : ℝ))) =
            ((CL + 1) ^ (8277 / 18200 : ℝ) *
              (CR + 1) ^ (3582 / 18200 : ℝ)) *
            ((X : ℝ) ^ (8277 / 18200 : ℝ) *
              (X : ℝ) ^ (-(1 / 180 : ℝ) * (3582 / 18200 : ℝ))) *
            Log ^ ((2 : ℝ) * (8277 / 18200 : ℝ)) := by ring
        _ = ((CL + 1) ^ (8277 / 18200 : ℝ) *
              (CR + 1) ^ (3582 / 18200 : ℝ)) *
            (X : ℝ) ^ (82571 / 182000 : ℝ) *
            Log ^ (8277 / 9100 : ℝ) := by
          rw [← Real.rpow_add hXpos]
          congr 2 <;> norm_num

theorem exists_inghamGabrielPoleClearedError_centerMoment_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      inghamFixedGabrielCenterMoment
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) ≤
          C * (X : ℝ) ^ (82571 / 118590 : ℝ) *
            (1 + Real.log (X : ℝ)) ^ 2 := by
  obtain ⟨K, hK, hpowered⟩ :=
    exists_inghamGabrielPoleClearedError_centerMoment_powered_le_polylog
  let C : ℝ := K ^ (18200 / 11859 : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX
  let I0 : ℝ := inghamFixedGabrielCenterMoment
    (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ)
  let Log : ℝ := 1 + Real.log (X : ℝ)
  have hI0 : 0 ≤ I0 := inghamFixedGabrielCenterMoment_nonneg _ _
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hLog1 : 1 ≤ Log := by
    dsimp only [Log]
    linarith [Real.log_nonneg hXone]
  have hLog0 : 0 ≤ Log := by positivity
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _)
    (hpowered hX) (by norm_num : (0 : ℝ) ≤ 18200 / 11859)
  have hlogExponent : (5518 / 3953 : ℝ) ≤ 2 := by norm_num
  have hlogMono : Log ^ (5518 / 3953 : ℝ) ≤ Log ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLog1 hlogExponent
  calc
    I0 = (I0 ^ (11859 / 18200 : ℝ)) ^ (18200 / 11859 : ℝ) := by
      rw [← Real.rpow_mul hI0]
      norm_num
    _ ≤ (K * (X : ℝ) ^ (82571 / 182000 : ℝ) *
          Log ^ (8277 / 9100 : ℝ)) ^ (18200 / 11859 : ℝ) := hpow
    _ = C * (X : ℝ) ^ (82571 / 118590 : ℝ) *
          Log ^ (5518 / 3953 : ℝ) := by
      dsimp only [C]
      rw [Real.mul_rpow (mul_nonneg hK (Real.rpow_nonneg hXpos.le _))
          (Real.rpow_nonneg hLog0 _),
        Real.mul_rpow hK (Real.rpow_nonneg hXpos.le _),
        ← Real.rpow_mul hXpos.le, ← Real.rpow_mul hLog0]
      congr 2 <;> norm_num
    _ ≤ C * (X : ℝ) ^ (82571 / 118590 : ℝ) * Log ^ (2 : ℝ) := by
      gcongr
    _ = C * (X : ℝ) ^ (82571 / 118590 : ℝ) * Log ^ 2 := by
      rw [Real.rpow_two]

end

end RHTower.Sieve

