import GaloisForLFunctions.RHTower.LogarithmicReconstructionAction
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# First and second variations of the arithmetic reconstruction action

The actual Möbius vector is stationary in every real coefficient
direction. Its Hessian is the signed doubled-source form, with no
positivity premise or conclusion.
-/

noncomputable section

namespace RHTower

theorem hasDerivAt_logarithmicReconstructionAction_mobius_line
    (v : ℕ → ℝ) (f : ℝ → ℝ) (T z : ℝ) :
    HasDerivAt (fun q => logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) + q * v n) f T)
        (-2 * z * logarithmicWeightedDilation v
          (logarithmicWeightedDilation v (logarithmicDilationSum f)) T) z := by
  have he : (fun q => logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) + q * v n) f T) =
      fun q => logarithmicMobiusInverse f T - q ^ 2 * logarithmicWeightedDilation v
        (logarithmicWeightedDilation v (logarithmicDilationSum f)) T :=
    funext (logarithmicReconstructionAction_mobius_line v f T)
  rw [he]
  exact ((((hasDerivAt_id z).pow 2).mul_const _).const_sub _).congr_deriv (by norm_num)

theorem hasDerivAt_logarithmicReconstructionAction_mobius_zero
    (v : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    HasDerivAt (fun q => logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) + q * v n) f T) 0 0 := by
  simpa only [mul_zero, zero_mul] using
    hasDerivAt_logarithmicReconstructionAction_mobius_line v f T 0

theorem hasDerivAt_deriv_logarithmicReconstructionAction_mobius_line
    (v : ℕ → ℝ) (f : ℝ → ℝ) (T z : ℝ) :
    HasDerivAt (fun q => deriv (fun r => logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) + r * v n) f T) q)
        (-2 * logarithmicWeightedDilation v
          (logarithmicWeightedDilation v (logarithmicDilationSum f)) T) z := by
  have he : (fun q => deriv (fun r => logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) + r * v n) f T) q) =
      fun q => -2 * q * logarithmicWeightedDilation v
        (logarithmicWeightedDilation v (logarithmicDilationSum f)) T :=
    funext (fun q => (hasDerivAt_logarithmicReconstructionAction_mobius_line v f T q).deriv)
  rw [he]
  exact (((hasDerivAt_id z).const_mul (-2)).mul_const _).congr_deriv (by ring)

end RHTower
