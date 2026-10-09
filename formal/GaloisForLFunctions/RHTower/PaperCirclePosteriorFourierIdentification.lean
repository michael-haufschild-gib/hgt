import GaloisForLFunctions.RHTower.PaperCircleCalibrationPrediction

/-! # Complete Fourier identification of native conditional posteriors

The source's finite inversion formula reconstructs the actual posterior density
from its character means. Consequently zero calibration is exactly agreement of
all conditional Fourier observables, at every output.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem paperCircleNextPosterior_fourier_inversion (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z x : Grid (l+r+10)) :
    (paperCircleNextPosterior a l r k i s t z x : ℂ) =
      (Period.side (l+r+10) : ℂ) * ∑ u, paperCircleNextCharacterMean a l r k i s t (-u) z * chi u x := by
  have hf (u : Grid (l+r+10)) :
      fc (fun y => (paperCircleNextPosterior a l r k i s t z y : ℂ)) u =
        (Period.side (l+r+10) : ℂ) * paperCircleNextCharacterMean a l r k i s t (-u) z := by
    simp only [fc, expU, Complex.real_smul, paperCircleNextCharacterMean, Law.Cx]
  calc
    _ = ∑ u, fc (fun y => (paperCircleNextPosterior a l r k i s t z y : ℂ)) u * chi u x :=
      (invert_fc _ x).symm
    _ = _ := by simp only [hf, mul_assoc, Finset.mul_sum]

theorem paperCircleNextPosterior_eq_iff_characters (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (z : Grid (l+r+10)) :
    paperCircleNextPosterior a l r k i s t z = paperCircleNextPosterior a l r k i v τ z ↔
      ∀ u, paperCircleNextCharacterMean a l r k i s t u z =
        paperCircleNextCharacterMean a l r k i v τ u z := by
  constructor
  · intro h u
    exact congrArg (fun P : Law (Grid (l+r+10)) => P.Cx (chi u)) h
  · intro h
    apply Law.ext
    intro x
    apply Complex.ofReal_inj.mp
    rw [paperCircleNextPosterior_fourier_inversion, paperCircleNextPosterior_fourier_inversion]
    simp only [h]

/-- All posterior Fourier observables agree exactly when the native reference debt vanishes. -/
theorem paperCirclePosteriorCalibration_eq_zero_iff_characters (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10))) (t τ : ℝ≥0) :
    paperCirclePosteriorCalibration a l r k i s v t τ = 0 ↔
      ∀ z u, paperCircleNextCharacterMean a l r k i s t u z =
        paperCircleNextCharacterMean a l r k i v τ u z := by
  rw [paperCirclePosteriorCalibration_eq_zero_iff]
  constructor
  · intro h z
    exact (paperCircleNextPosterior_eq_iff_characters a l r k i s v t τ z).mp (h z)
  · intro h z
    exact (paperCircleNextPosterior_eq_iff_characters a l r k i s v t τ z).mpr (h z)

end
end RHTower
