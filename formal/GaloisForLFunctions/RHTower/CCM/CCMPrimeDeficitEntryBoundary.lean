import GaloisForLFunctions.RHTower.LogarithmicVariableEntryContinuity
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitNoetherAction
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitShortQuadraticWork

/-!
# Removing the moving square-root cutoff boundary

The short quadratic work has an explicit entry boundary. Adding that
boundary produces a continuous function: each remaining summand vanishes
at its activation time. This removes cutoff jumps without assuming signed
arithmetic cancellation.
-/

noncomputable section
open Set
open scoped BigOperators

namespace RHTower

theorem continuous_ccmPrimeDeficitDilationSource : Continuous ccmPrimeDeficitDilationSource := by
  have h := continuous_logarithmicVariableEntrySum
    (fun n t => ccmLogChebyshevDeficitPrimitive (t - Real.log n))
    (fun n _ => continuous_ccmLogChebyshevDeficitPrimitive.comp
      (continuous_id.sub continuous_const))
    (fun n _ => by simp [ccmLogChebyshevDeficitPrimitive])
  exact h.congr (fun T => ccmLogChebyshevDeficitPrimitive_dilation_conservation T)

theorem continuous_ccmPrimeDeficitDilationRemainder : Continuous ccmPrimeDeficitDilationRemainder :=
  (continuous_ccmPrimeDeficitDilationSource.sub
    (continuous_const.mul (Real.continuous_exp.sub continuous_const))).add
      (continuous_const.mul continuous_id)

def ccmPrimeDeficitShortBoundaryCorrection (T : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
    moebiusCoeff n * ccmPrimeDeficitDilationRemainder (Real.log n)

def ccmPrimeDeficitShortBoundaryWork (T : ℝ) : ℝ :=
  ccmPrimeDeficitShortQuadraticWork T + ccmPrimeDeficitShortBoundaryCorrection T

theorem ccmLogChebyshevDeficitPrimitive_sub_shortBoundaryWork {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortBoundaryWork T =
      2 * logarithmicVariableEntrySum
        (fun n u => moebiusCoeff n *
          (ccmPrimeDeficitDilationRemainder (2 * u - Real.log n) -
            ccmPrimeDeficitDilationRemainder (Real.log n))) (T / 2) := by
  have hU : ⌊Real.exp (T / 2)⌋₊ ≤ ⌊Real.exp T⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hT]))
  rw [ccmPrimeDeficitShortBoundaryWork, sub_add_eq_sub_sub,
    ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork hT,
    logarithmicShortMobiusInverse_eq_prefix _ _ hU]
  simp only [ccmPrimeDeficitShortBoundaryCorrection, logarithmicVariableEntrySum,
    show 2 * (T / 2) = T by ring, moebiusCoeff, mul_sub, Finset.sum_sub_distrib]

theorem continuousOn_ccmPrimeDeficitShortBoundaryWork :
    ContinuousOn ccmPrimeDeficitShortBoundaryWork (Ici 0) := by
  have h := continuous_logarithmicVariableEntrySum
    (fun n u => moebiusCoeff n *
      (ccmPrimeDeficitDilationRemainder (2 * u - Real.log n) -
        ccmPrimeDeficitDilationRemainder (Real.log n)))
    (fun n _ => continuous_const.mul
      ((continuous_ccmPrimeDeficitDilationRemainder.comp
        ((continuous_const.mul continuous_id).sub continuous_const)).sub continuous_const))
    (fun n _ => by rw [show 2 * Real.log n - Real.log n = Real.log n by ring]; simp)
  have hc := continuous_ccmLogChebyshevDeficitPrimitive.sub
    ((h.comp (continuous_id.div_const 2)).const_mul 2)
  apply hc.continuousOn.congr
  intro T hT
  dsimp only [Pi.sub_apply, Function.comp_apply, id_eq]
  have he := ccmLogChebyshevDeficitPrimitive_sub_shortBoundaryWork hT
  linarith only [he]

end RHTower
