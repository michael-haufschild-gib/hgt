import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitShortDilationAction
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEntryBoundaryBounds

/-!
# A continuous first variation after arithmetic boundary correction

The explicit entry correction completes the earlier dilation action.
Its parameter derivative is continuous in nonnegative logarithmic time,
and its half derivative differs from the actual signed prime deficit by
only a quadratic polynomial. This does not assert invariance or a bound
on the derivative itself.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RHTower

def ccmPrimeDeficitBoundaryDilationAction (T z : ℝ) : ℝ :=
  ccmPrimeDeficitShortCompletedDilationAction T z +
    2 * z * ccmPrimeDeficitShortBoundaryCorrection T

theorem hasDerivAt_ccmPrimeDeficitBoundaryDilationAction_zero {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (ccmPrimeDeficitBoundaryDilationAction T)
      (2 * ccmPrimeDeficitShortBoundaryWork T) 0 := by
  have h := (hasDerivAt_ccmPrimeDeficitShortCompletedDilationAction_zero hT).add
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (ccmPrimeDeficitShortBoundaryCorrection T))
  exact h.congr_deriv (by dsimp only [ccmPrimeDeficitShortBoundaryWork]; ring)

theorem continuousOn_ccmPrimeDeficitBoundaryDilationAction_deriv :
    ContinuousOn (fun T => deriv (ccmPrimeDeficitBoundaryDilationAction T) 0) (Ici 0) := by
  apply (continuousOn_ccmPrimeDeficitShortBoundaryWork.const_mul 2).congr
  intro T hT
  exact (hasDerivAt_ccmPrimeDeficitBoundaryDilationAction_zero hT).deriv

theorem ccmLogChebyshevDeficitPrimitive_boundary_dilation_conservation
    {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      deriv (ccmPrimeDeficitBoundaryDilationAction T) 0 / 2 +
        2 * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, moebiusCoeff n *
          (ccmPrimeDeficitDilationRemainder (T - Real.log n) -
            ccmPrimeDeficitDilationRemainder (Real.log n)) := by
  rw [(hasDerivAt_ccmPrimeDeficitBoundaryDilationAction_zero hT).deriv,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have h := ccmLogChebyshevDeficitPrimitive_sub_shortBoundaryWork hT
  simp only [logarithmicVariableEntrySum, show 2 * (T / 2) = T by ring] at h
  linarith only [h]

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_boundaryDilation_deriv_le
    {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T -
      deriv (ccmPrimeDeficitBoundaryDilationAction T) 0 / 2| ≤
        (T ^ 2 + 34 * T + 112) / 8 := by
  rw [(hasDerivAt_ccmPrimeDeficitBoundaryDilationAction_zero hT).deriv,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact abs_ccmLogChebyshevDeficitPrimitive_sub_shortBoundaryWork_le hT

theorem tendsto_ccmPrimeDeficitBoundaryDilationAction_normalized_error :
    Tendsto (fun T => Real.exp (-(T / 2)) *
      (ccmLogChebyshevDeficitPrimitive T -
        deriv (ccmPrimeDeficitBoundaryDilationAction T) 0 / 2)) atTop (𝓝 0) := by
  apply tendsto_ccmPrimeDeficitShortBoundaryWork_normalized_error.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [(hasDerivAt_ccmPrimeDeficitBoundaryDilationAction_zero hT).deriv,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]

end RHTower
