import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielPoleClearedBound
import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGaussianTranslatedMomentPolylog
import GaloisForLFunctions.RHTower.Sieve.InghamMovingRightGaussianTranslatedMoment
import GaloisForLFunctions.RHTower.Sieve.InghamGabrielCenterMoment
import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielConstantBudget

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- The moving-Gabriel center moment with all dependence on the counting line exposed. The
constant `C` comes only from the critical-line moment and is independent of `sigma`; degeneration
as `sigma → 1` is confined to the explicit moving-right factor. -/
theorem exists_inghamGabrielPoleClearedError_uniformCenterMoment_le_explicit :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      ∀ {X : ℕ}, 4 ≤ X →
        inghamUniformGabrielCenterMoment sigma
          (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) ≤
            C *
              (1 + inghamMovingRightTranslatedExplicitConstant
                ((9 / 100 : ℝ) * (1 - sigma))) *
              (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
              (1 + Real.log (X : ℝ)) ^
                (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨CL, hCL, hleft⟩ :=
    exists_inghamGabrielPoleClearedError_critical_translatedMoment_le_polylog
  refine ⟨CL + 1, by positivity, ?_⟩
  intro sigma hsigma0 hsigma1 X hX
  let delta : ℝ := (9 / 100 : ℝ) * (1 - sigma)
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdelta1 : delta ≤ 1 := by
    dsimp only [delta]
    nlinarith
  let CR : ℝ := inghamMovingRightTranslatedExplicitConstant delta
  have hCR : 0 ≤ CR := by
    dsimp only [CR, inghamMovingRightTranslatedExplicitConstant]
    positivity
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  let Log : ℝ := 1 + Real.log (X : ℝ)
  have hLog1 : 1 ≤ Log := by
    dsimp only [Log]
    linarith [Real.log_nonneg hXone]
  have hLog0 : 0 ≤ Log := hLog1.trans' (by norm_num)
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
        have h :=
          inghamGabrielPoleClearedError_movingRight_translatedMoment_le_explicit
            hdelta hdelta1 hX z (by
              dsimp only [delta]
              rw [hz]
              unfold inghamUniformGabrielRightEdge
              ring)
        dsimp only [Right, CR]
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg hXpos.le _)))
  let cs : ℝ := inghamUniformGabrielCriticalShare sigma
  let rs : ℝ := inghamUniformGabrielRightShare sigma
  let E : ℝ := inghamUniformGabrielConservativeExponent sigma
  have hshape :
      Left ^ cs * Right ^ rs =
        ((CL + 1) ^ cs * (CR + 1) ^ rs) *
          (X : ℝ) ^ E * Log ^ (2 * cs) := by
    dsimp only [Left, Right, cs, rs, E]
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
  have hcs1 : cs ≤ 1 := by
    exact inghamUniformGabrielCriticalShare_le_one hsigma0 hsigma1le
  have hrs1 : rs ≤ 1 := by
    exact inghamUniformGabrielRightShare_le_one hsigma1le
  have hcoeff :
      (CL + 1) ^ cs * (CR + 1) ^ rs ≤ (CL + 1) * (CR + 1) := by
    exact mul_le_mul
      (Real.rpow_le_self_of_one_le (by linarith) hcs1)
      (Real.rpow_le_self_of_one_le (by linarith) hrs1)
      (Real.rpow_nonneg (by positivity) _)
      (by positivity)
  have htail0 : 0 ≤ (X : ℝ) ^ E * Log ^ (2 * cs) :=
    mul_nonneg (Real.rpow_nonneg hXpos.le _) (Real.rpow_nonneg hLog0 _)
  calc
    inghamUniformGabrielCenterMoment sigma
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) ≤
      Left ^ cs * Right ^ rs := hinterp
    _ = ((CL + 1) ^ cs * (CR + 1) ^ rs) *
          (X : ℝ) ^ E * Log ^ (2 * cs) := hshape
    _ = ((CL + 1) ^ cs * (CR + 1) ^ rs) *
          ((X : ℝ) ^ E * Log ^ (2 * cs)) := by ring
    _ ≤ ((CL + 1) * (CR + 1)) *
          ((X : ℝ) ^ E * Log ^ (2 * cs)) :=
      mul_le_mul_of_nonneg_right hcoeff htail0
    _ = (CL + 1) * (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
      dsimp only [CR, delta, E, cs, Log]
      ring

end

end RHTower.Sieve
