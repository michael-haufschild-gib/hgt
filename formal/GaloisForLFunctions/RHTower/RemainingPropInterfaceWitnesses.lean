import GaloisForLFunctions.RHTower.GammaFactorialCompleteToricJetClosureUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeEulerOrientationNorm

/-!
# Remaining Riemann-tower proposition-interface witnesses

Canonical inhabitants for the toric balance lattice and both finite-tail Euler orientation modes.
-/

namespace GaloisForLFunctions.RHTower

/-- The origin belongs to the complete Gamma-factorial toric balance lattice. -/
theorem gammaFactorialToricBalanced_zero :
    GammaFactorialToricBalanced 0 0 0 0 0 0 0 := by
  simp [GammaFactorialToricBalanced]

/-- Every prime orientation is same-sheet Euler-gauge equivalent to itself. -/
theorem primeEulerTailGaugeEquivalent_refl
    {P : Type*} (ε : P → Bool) :
    PrimeEulerTailGaugeEquivalent ε ε := by
  rw [primeEulerTailGaugeEquivalent_iff_eventuallyEqual]
  simp [GaloisForLFunctions.HTGeometry.PrimeOrientationsEventuallyEqual]

/-- Every prime orientation is opposite-sheet Euler-norm complementary to its Boolean negation. -/
theorem primeEulerTailNormComplementary_not
    {P : Type*} (ε : P → Bool) :
    PrimeEulerTailNormComplementary ε (fun p => !(ε p)) := by
  rw [primeEulerTailNormComplementary_iff_eventuallyOpposite]
  simp [GaloisForLFunctions.HTGeometry.PrimeOrientationsEventuallyOpposite]

end GaloisForLFunctions.RHTower
