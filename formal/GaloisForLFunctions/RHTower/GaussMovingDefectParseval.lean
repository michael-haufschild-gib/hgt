import GaloisForLFunctions.RHTower.GaussRatioPowerMovingTranslation

/-!
# Exact Parseval identity for a Gauss moving defect

This generic identity isolates the sampled-ratio defect as a diagonal Fourier weight for every
input vector.  Concrete propagation modules can therefore prove lattice-energy bounds without
repeating Fourier-basis coercion arguments.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions
open scoped ENNReal

noncomputable section

def gaussMovingDefectVector {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (i : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussShiftedBlockOf hm k p i u -
    gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) u

def gaussMovingDefectEnergy {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal
    (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
      ‖gaussSampleRatioDefect k p j i‖ ^ 2)

theorem ofReal_norm_gaussMovingDefectVector_sq_eq_energy
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (i : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ENNReal.ofReal (‖gaussMovingDefectVector hm k p i u‖ ^ (2 : ℝ)) =
      gaussMovingDefectEnergy k p i u := by
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussMovingDefectVector hm k p i u with hw
  have hcoeff : ∀ j : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ =
        ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ *
          ‖gaussSampleRatioDefect k p j i‖ := by
    intro j
    have hsub : fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j =
        fourierCoeff ((gaussShiftedBlockOf hm k p i u : AddCircle (1 : ℝ) → ℂ)) j -
          fourierCoeff ((gaussRotationBlock
            ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) u :
              AddCircle (1 : ℝ) → ℂ)) j := by
      rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, hw,
        gaussMovingDefectVector, map_sub]
      rfl
    rw [hsub, norm_fourierCoeff_shiftedBlockOf_sub_rotation hm k p]
  have hcongr : ∀ j : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) =
        ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
          ‖gaussSampleRatioDefect k p j i‖ ^ 2 := by
    intro j
    rw [hcoeff j, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      ← Real.rpow_natCast (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖) 2,
      ← Real.rpow_natCast (‖gaussSampleRatioDefect k p j i‖) 2]
    norm_num
  have hsummable : Summable fun j : ℤ =>
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr w)
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun j => ?_
    rw [fourierBasis_repr]
  have hsummable' : Summable fun j : ℤ =>
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j i‖ ^ 2 := hsummable.congr hcongr
  rw [gaussMovingDefectEnergy]
  change ENNReal.ofReal (‖w‖ ^ (2 : ℝ)) = _
  rw [norm_sq_eq_tsum_fourierCoeff w, tsum_congr hcongr,
    ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable']

end

end RHTower
