import GaloisForLFunctions.RHTower.GaussRelativeOneStep
import GaloisForLFunctions.RHTower.GaussSpikeDefectVanishing
import GaloisForLFunctions.HTGeometry.FourierInnerCoefficientBound

/-!
# The one-step deviation, read through a pairing

`R − M` splits into two terms, each of which carries exactly one moving-translation defect.
Pairing against a fixed vector and moving every normalized shifted block onto the *left* slot by
adjointness turns both terms into coefficientwise sums

`Σ_j ‖X̂(j)‖ ‖Ŷ(j)‖ ‖defect_j‖`,

where `X` is built from the fixed vector and `Y` from the vector `R` is applied to.  No operator
norm of a normalized shifted block occurs anywhere, which is what makes the estimate survive the
spike those blocks create at the moving frequency.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The two-term split of the one-step deviation.** -/
theorem gaussPrincipalStep_sub_amplitude_eq (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (n : ℤ)
    (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussPrincipalStepBlock hm k p hp n v -
        gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) v
      = gaussPrimeScaleBlock hp (gaussShiftedBlockDiag hm k p n
          (gaussPrimeScaleInvSqBlock hp
            (gaussShiftedBlockOf hm k p n (gaussPrimeScaleBlock hp v) -
              gaussTranslationBlock ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
                (gaussPrimeScaleBlock hp v))))
        + gaussPrimeScaleBlock hp
            (gaussShiftedBlockDiag hm k p n
                (gaussPrimeScaleInvSqBlock hp
                  (gaussTranslationBlock ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
                    (gaussPrimeScaleBlock hp v))) -
              gaussTranslationBlock (-((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)))
                (gaussPrimeScaleInvSqBlock hp
                  (gaussTranslationBlock ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
                    (gaussPrimeScaleBlock hp v)))) := by
  set δ : AddCircle (1 : ℝ) := ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) with hδ
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := gaussPrimeScaleBlock hp v with hw
  set a : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockOf hm k p n w with ha
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := gaussTranslationBlock δ w with hb
  have hM : gaussMovingAmplitudeBlock hp δ v
      = gaussPrimeScaleBlock hp
        (gaussTranslationBlock (-δ) (gaussPrimeScaleInvSqBlock hp b)) := by
    rw [hb, hw, gaussPrimeScaleBlock_translate_invSq_translate hp δ v]
  rw [gaussPrincipalStepBlock_apply, hM, ← hw, ← ha, ← map_sub, ← map_add]
  congr 1
  rw [map_sub (gaussPrimeScaleInvSqBlock hp), ← gaussShiftedBlockDiag_sub]
  abel

set_option maxHeartbeats 1000000 in
/-- **The pairing bound for the one-step deviation.** -/
theorem ofReal_norm_inner_gaussPrincipalStep_sub_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (n : ℤ)
    (g v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ENNReal.ofReal ‖(inner ℂ g (gaussPrincipalStepBlock hm k p hp n v -
        gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) v) : ℂ)‖
      ≤ (∑' j : ℤ, ENNReal.ofReal
          (‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm k p n
              (gaussPrimeScaleBlock hp g)) : AddCircle (1 : ℝ) → ℂ)) j‖ *
            ‖fourierCoeff ((gaussPrimeScaleBlock hp v : AddCircle (1 : ℝ) → ℂ)) j‖ *
            ‖gaussSampleRatioDefect k p j n‖))
        + (∑' j : ℤ, ENNReal.ofReal
          (‖fourierCoeff ((gaussPrimeScaleBlock hp g : AddCircle (1 : ℝ) → ℂ)) j‖ *
            ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp
              (gaussTranslationBlock ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
                (gaussPrimeScaleBlock hp v)) : AddCircle (1 : ℝ) → ℂ)) j‖ *
            ‖gaussSampleRatioDefect k p j n‖)) := by
  set δ : AddCircle (1 : ℝ) := ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) with hδ
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := gaussPrimeScaleBlock hp v with hw
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := gaussTranslationBlock δ w with hb
  set z : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleInvSqBlock hp b with hz
  set d : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockOf hm k p n w - b with hd
  set X : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm k p n (gaussPrimeScaleBlock hp g))
    with hX
  -- first term: move `B`, `S`, `B^{-2}` to the left slot
  have hterm1 : (inner ℂ g (gaussPrimeScaleBlock hp
        (gaussShiftedBlockDiag hm k p n (gaussPrimeScaleInvSqBlock hp d))) : ℂ)
      = inner ℂ X d := by
    rw [← gaussPrimeScaleBlock_inner hp g, ← gaussShiftedBlockOf_inner hm k p n,
      ← gaussPrimeScaleInvSqBlock_inner hp, hX]
  -- second term: move `B` to the left slot
  have hterm2 : (inner ℂ g (gaussPrimeScaleBlock hp
        (gaussShiftedBlockDiag hm k p n z - gaussTranslationBlock (-δ) z)) : ℂ)
      = inner ℂ (gaussPrimeScaleBlock hp g) (gaussShiftedBlockDiag hm k p n z -
          gaussTranslationBlock (-δ) z) := by
    rw [← gaussPrimeScaleBlock_inner hp g]
  rw [gaussPrincipalStep_sub_amplitude_eq hm k p hp n v, ← hw, ← hb, ← hz, ← hd, inner_add_right,
    hterm1, hterm2]
  refine le_trans (ENNReal.ofReal_le_ofReal (norm_add_le _ _)) ?_
  rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine add_le_add ?_ ?_
  · refine le_trans (ofReal_norm_inner_le_tsum_fourierCoeff X d) ?_
    refine ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hcoef : ‖fourierCoeff ((d : AddCircle (1 : ℝ) → ℂ)) j‖
        = ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ * ‖gaussSampleRatioDefect k p j n‖ := by
      rw [hd, fourierCoeff_sub_lp, hb, ← gaussRotationBlock_eq_translation]
      exact norm_fourierCoeff_shiftedBlockOf_sub_rotation hm k p n j w
    rw [hcoef, ← mul_assoc]
  · refine le_trans (ofReal_norm_inner_le_tsum_fourierCoeff _ _) ?_
    refine ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hcoef : ‖fourierCoeff (((gaussShiftedBlockDiag hm k p n z -
          gaussTranslationBlock (-δ) z : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
            AddCircle (1 : ℝ) → ℂ)) j‖
        = ‖fourierCoeff ((z : AddCircle (1 : ℝ) → ℂ)) j‖ * ‖gaussSampleRatioDefect k p j n‖ := by
      rw [fourierCoeff_sub_lp, ← gaussRotationBlockInv_eq_translation]
      exact norm_fourierCoeff_shiftedBlockDiag_sub_rotationInv hm k p n j z
    rw [hcoef, ← mul_assoc]

end

end RHTower
