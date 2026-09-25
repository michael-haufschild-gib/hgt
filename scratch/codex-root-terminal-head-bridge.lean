import GaloisForLFunctions.RHTower.MobiusDivisorAdaptiveTerminalCriticalSource

noncomputable section
open Finset
namespace RHTower

theorem criticalContinuousAbel_nat_eq_dilation_sum (M : ℕ) (hM : 1 ≤ M) :
    criticalContinuousAbel (M : ℝ) =
      ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d := by
  have hchild := criticalChild_eq_criticalContinuousAbel M 1 (by omega) (by simpa using hM)
  have hclip : divisorPrimeClipWeight M 1 = 0 := by
    simp [divisorPrimeClipWeight]
  simpa [mobiusDivisorCriticalChildSource, hclip] using hchild.symm

end RHTower
