import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielPoleClearedBound
import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGaussianTranslatedMomentPolylog
import GaloisForLFunctions.RHTower.Sieve.InghamMovingRightGaussianTranslatedMoment
import GaloisForLFunctions.RHTower.Sieve.InghamGabrielCenterMoment

open Complex MeasureTheory Set

namespace RHTower.Sieve

/-! # Moving-Gabriel center moment with retained polylogarithmic loss -/

noncomputable section

/-- Actual moving center moment obeys the conservative uniform Gabriel exponent. The constant may
depend on the counting line `sigma`, while the power coefficient is the explicit function already
proved bounded by `16/5 * (1 - sigma)`. -/
theorem exists_inghamGabrielPoleClearedError_uniformCenterMoment_le_polylog
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      inghamUniformGabrielCenterMoment sigma
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) ≤
          C * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) := by
  let delta : ℝ := (9 / 100 : ℝ) * (1 - sigma)
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdelta1 : delta ≤ 1 := by
    dsimp only [delta]
    nlinarith
  obtain ⟨CL, hCL, hleft⟩ :=
    exists_inghamGabrielPoleClearedError_critical_translatedMoment_le_polylog
  obtain ⟨CR, hCR, hright⟩ :=
    exists_inghamGabrielPoleClearedError_movingRight_translatedMoment_le
      hdelta hdelta1
  let K : ℝ :=
    (CL + 1) ^ inghamUniformGabrielCriticalShare sigma *
      (CR + 1) ^ inghamUniformGabrielRightShare sigma
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  let Log : ℝ := 1 + Real.log (X : ℝ)
  have hLog1 : 1 ≤ Log := by
    dsimp only [Log]
    linarith [Real.log_nonneg hXone]
  have hLog0 : 0 ≤ Log := by positivity
  let Left : ℝ := (CL + 1) * (X : ℝ) * Log ^ 2
  let Right : ℝ := (CR + 1) * (X : ℝ) ^ (-delta)
  have hLeft : 0 < Left := by dsimp only [Left]; positivity
  have hRight : 0 < Right := by dsimp only [Right]; positivity
  have hinterp :=
    inghamUniformGabrielCenterMoment_le_shares_of_vertical_continuous
      hsigma0 hsigma1le
      (fun z hz => continuous_poleCleared_vertical_of_half_le X hz)
      (X : ℝ) Left Right hLeft hRight
      (diffContOnCl_inghamUniformGabrielScalarFamily_poleCleared
        hsigma0 hsigma1le X (kappa := 1) (T := (X : ℝ)) hXpos.le)
      (bddAbove_inghamUniformGabrielScalarFamily_poleCleared
        hsigma0 hsigma1le X (kappa := 1) (T := (X : ℝ)) (by norm_num) hXpos)
      (fun z hz => by
        have h := hleft hX z hz
        dsimp only [Left, Log]
        exact h.trans (by
          gcongr
          linarith))
      (fun z hz => by
        have h := hright hX z (by
          dsimp only [delta]
          rw [hz]
          unfold inghamUniformGabrielRightEdge
          ring)
        dsimp only [Right]
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg hXpos.le _)))
  calc
    inghamUniformGabrielCenterMoment sigma
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) ≤
      Left ^ inghamUniformGabrielCriticalShare sigma *
        Right ^ inghamUniformGabrielRightShare sigma := hinterp
    _ = K * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
        Log ^ (2 * inghamUniformGabrielCriticalShare sigma) := by
      dsimp only [Left, Right, K]
      rw [Real.mul_rpow (mul_nonneg (by positivity) hXpos.le)
          (pow_nonneg hLog0 2),
        Real.mul_rpow (by positivity) hXpos.le,
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hXpos.le _),
        ← Real.rpow_natCast Log 2, ← Real.rpow_mul hLog0,
        ← Real.rpow_mul hXpos.le]
      calc
        ((CL + 1) ^ inghamUniformGabrielCriticalShare sigma *
              (X : ℝ) ^ inghamUniformGabrielCriticalShare sigma *
              Log ^ ((2 : ℝ) * inghamUniformGabrielCriticalShare sigma)) *
            ((CR + 1) ^ inghamUniformGabrielRightShare sigma *
              (X : ℝ) ^
                (-delta * inghamUniformGabrielRightShare sigma)) =
          ((CL + 1) ^ inghamUniformGabrielCriticalShare sigma *
              (CR + 1) ^ inghamUniformGabrielRightShare sigma) *
            ((X : ℝ) ^ inghamUniformGabrielCriticalShare sigma *
              (X : ℝ) ^
                (-delta * inghamUniformGabrielRightShare sigma)) *
            Log ^ ((2 : ℝ) * inghamUniformGabrielCriticalShare sigma) := by ring
        _ = ((CL + 1) ^ inghamUniformGabrielCriticalShare sigma *
              (CR + 1) ^ inghamUniformGabrielRightShare sigma) *
            (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            Log ^ (2 * inghamUniformGabrielCriticalShare sigma) := by
          rw [← Real.rpow_add hXpos]
          congr 2
          unfold inghamUniformGabrielConservativeExponent
            inghamUniformGabrielConservativeRightMomentExponent
          dsimp only [delta]
          ring

end

end RHTower.Sieve
