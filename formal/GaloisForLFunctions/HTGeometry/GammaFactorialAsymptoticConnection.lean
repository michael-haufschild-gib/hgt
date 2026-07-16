import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp
import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The source-defined factorial connection of the Gamma pole clock

The reciprocal-Gamma microscope at the pole `-n` has the canonical scale
`(-1)^(n+1)/n!`.  Its norm therefore gives a positive scalar transport whose link ratios are
`1/(n+1)`.  The forward transport tends to zero and its inverse tends to infinity, so this actual
Gamma source clock has a nontrivial bounded-uniformization class.

This file deliberately does not identify the pole-index clock with the intrinsic differential-jet
grading.  That moving-base bridge is a separate open theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- The adjacent link of the positive Gamma factorial pole connection. -/
noncomputable def gammaFactorialConnectionLink (n : ℕ) : ℝ :=
  1 / (n + 1 : ℕ)

/-- Ordered transport from the first Gamma pole scale through grade `n`. -/
noncomputable def gammaFactorialConnectionTransport (n : ℕ) : ℝ :=
  1 / (n.factorial : ℝ)

@[simp] theorem gammaFactorialConnectionTransport_zero :
    gammaFactorialConnectionTransport 0 = 1 := by
  simp [gammaFactorialConnectionTransport]

/-- The exact factorial connection recursion. -/
theorem gammaFactorialConnectionTransport_succ (n : ℕ) :
    gammaFactorialConnectionTransport (n + 1) =
      gammaFactorialConnectionLink n * gammaFactorialConnectionTransport n := by
  simp [gammaFactorialConnectionTransport, gammaFactorialConnectionLink,
    Nat.factorial_succ, mul_comm]

/-- The connection transport is the norm of the actual reciprocal-Gamma pole scale. -/
theorem norm_reciprocalGammaFactorialScale_eq_connectionTransport (n : ℕ) :
    ‖reciprocalGammaFactorialScale n‖ = gammaFactorialConnectionTransport n := by
  exact norm_reciprocalGammaFactorialScale n

/-- The forward pole-clock transport collapses to the boundary. -/
theorem gammaFactorialConnectionTransport_tendsto_zero :
    Tendsto gammaFactorialConnectionTransport atTop (nhds 0) := by
  have h := tendsto_reciprocalGammaFactorialScale_zero.norm
  simpa only [norm_zero] using h.congr' (Eventually.of_forall fun n ↦
    norm_reciprocalGammaFactorialScale_eq_connectionTransport n)

@[simp] theorem gammaFactorialConnectionTransport_inv (n : ℕ) :
    (gammaFactorialConnectionTransport n)⁻¹ = (n.factorial : ℝ) := by
  simp [gammaFactorialConnectionTransport]

/-- The canonical algebraic flat gauge is not bounded: its factorial norm tends to infinity. -/
theorem gammaFactorialConnectionTransport_inv_tendsto_atTop :
    Tendsto (fun n ↦ (gammaFactorialConnectionTransport n)⁻¹) atTop atTop := by
  simpa using (tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop)

end GaloisForLFunctions.HTGeometry
