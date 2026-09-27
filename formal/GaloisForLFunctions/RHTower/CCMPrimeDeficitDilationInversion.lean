import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationConservation
import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction
import GaloisForLFunctions.RHTower.Mollifier

/-!
# Exact signed reconstruction from the elementary dilation source

The complete delay conservation law is invertible by the literal Möbius
coefficients. This reconstructs the original deficit, preserving every
sign and finite cutoff. Algebraic inversion is not a bound on its norm.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

/-- Every deficit value is the complete signed Möbius reconstruction of
the elementary source. No error estimate or RH premise is used. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (ArithmeticFunction.moebius n : ℝ) *
        ccmPrimeDeficitDilationSource (T - Real.log n) := by
  have hs : logarithmicDilationSum ccmLogChebyshevDeficitPrimitive =
      ccmPrimeDeficitDilationSource := by
    funext t
    simpa only [logarithmicDilationSum, logarithmicWeightedDilation, one_mul] using
      ccmLogChebyshevDeficitPrimitive_dilation_conservation t
  have hi := logarithmicMobiusInverse_dilationSum ccmLogChebyshevDeficitPrimitive hT
  rw [hs] at hi
  exact hi.symm

end RHTower
