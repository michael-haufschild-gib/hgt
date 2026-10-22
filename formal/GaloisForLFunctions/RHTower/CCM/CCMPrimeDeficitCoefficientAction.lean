import GaloisForLFunctions.RHTower.LogarithmicReconstructionTailSymmetry
import GaloisForLFunctions.RHTower.LogarithmicReconstructionVariation
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDivisorSource
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitNoetherAction

/-!
# Stationary arithmetic action and its exact long-tail symmetry

The source action is defined entirely from the elementary dilation source.
Its Möbius stationary value is the literal prime deficit. Every extension
of the correct square-root prefix has that same value, independently of
all later real coefficients. The signed Hessian is retained explicitly.
-/

noncomputable section
open Set

namespace RHTower

def ccmPrimeDeficitCoefficientAction (T : ℝ) (a : ℕ → ℝ) : ℝ :=
  logarithmicReconstructionAction a ccmPrimeDeficitDilationSource T

theorem ccmPrimeDeficitCoefficientAction_mobius_line (v : ℕ → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (z : ℝ) :
    ccmPrimeDeficitCoefficientAction T
      (fun n => (ArithmeticFunction.moebius n : ℝ) + z * v n) =
        ccmLogChebyshevDeficitPrimitive T - z ^ 2 *
          logarithmicWeightedDilation v
            (logarithmicWeightedDilation v ccmPrimeDeficitDivisorSource) T := by
  have hD : logarithmicMobiusInverse ccmPrimeDeficitDilationSource T =
      ccmLogChebyshevDeficitPrimitive T :=
    (ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation hT).symm
  have hH : logarithmicDilationSum ccmPrimeDeficitDilationSource = ccmPrimeDeficitDivisorSource :=
    funext logarithmicDilationSum_dilationSource_eq_divisorSource
  rw [ccmPrimeDeficitCoefficientAction, logarithmicReconstructionAction_mobius_line, hD, hH]

theorem hasDerivAt_ccmPrimeDeficitCoefficientAction_mobius_zero (v : ℕ → ℝ) (T : ℝ) :
    HasDerivAt (fun z => ccmPrimeDeficitCoefficientAction T
      (fun n => (ArithmeticFunction.moebius n : ℝ) + z * v n)) 0 0 :=
  hasDerivAt_logarithmicReconstructionAction_mobius_zero v ccmPrimeDeficitDilationSource T

theorem hasDerivAt_deriv_ccmPrimeDeficitCoefficientAction_mobius_line
    (v : ℕ → ℝ) (T z : ℝ) :
    HasDerivAt (fun q => deriv (fun r => ccmPrimeDeficitCoefficientAction T
      (fun n => (ArithmeticFunction.moebius n : ℝ) + r * v n)) q)
        (-2 * logarithmicWeightedDilation v
          (logarithmicWeightedDilation v ccmPrimeDeficitDivisorSource) T) z := by
  have hH : logarithmicDilationSum ccmPrimeDeficitDilationSource = ccmPrimeDeficitDivisorSource :=
    funext logarithmicDilationSum_dilationSource_eq_divisorSource
  simpa only [ccmPrimeDeficitCoefficientAction, hH] using
    hasDerivAt_deriv_logarithmicReconstructionAction_mobius_line v ccmPrimeDeficitDilationSource T z

/-- The actual deficit is independent of every coefficient beyond the
square-root prefix. The retained prefix consists of the literal Möbius values. -/
theorem ccmPrimeDeficitCoefficientAction_headExtension (v : ℕ → ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCoefficientAction T
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ v) =
        ccmLogChebyshevDeficitPrimitive T := by
  rw [ccmPrimeDeficitCoefficientAction, logarithmicReconstructionAction_mobiusHeadExtension]
  exact (ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation hT).symm

theorem ccmPrimeDeficitCoefficientAction_tail_translation
    (v w : ℕ → ℝ) (T q z : ℝ) :
    ccmPrimeDeficitCoefficientAction T
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ (fun n => v n + (q + z) * w n)) =
    ccmPrimeDeficitCoefficientAction T
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ (fun n => v n + q * w n)) := by
  simp only [ccmPrimeDeficitCoefficientAction, logarithmicReconstructionAction_mobiusHeadExtension]

theorem hasDerivAt_ccmPrimeDeficitCoefficientAction_tail_translation
    (v w : ℕ → ℝ) (T q : ℝ) :
    HasDerivAt (fun z => ccmPrimeDeficitCoefficientAction T
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ (fun n => v n + z * w n))) 0 q := by
  have he : (fun z => ccmPrimeDeficitCoefficientAction T
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ (fun n => v n + z * w n))) =
      fun _ => logarithmicMobiusInverse ccmPrimeDeficitDilationSource T := by
    funext z
    exact logarithmicReconstructionAction_mobiusHeadExtension _ _ T
  rw [he]
  exact hasDerivAt_const q _

theorem continuousOn_ccmPrimeDeficitCoefficientAction_headExtension (v : ℕ → ℝ) :
    ContinuousOn (fun T => ccmPrimeDeficitCoefficientAction T
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ v)) (Ici 0) := by
  apply continuous_ccmLogChebyshevDeficitPrimitive.continuousOn.congr
  intro T hT
  exact ccmPrimeDeficitCoefficientAction_headExtension v hT

end RHTower
