import GaloisForLFunctions.RHTower.Deninger.DeningerL1GreenCellCalculus
import GaloisForLFunctions.RHTower.Deninger.DeningerDampedWeightedSourceBoundary

/-!
# The complete original Green boundary of the damped source

The actual damping-two source has an original local Green primitive at every
prime period. Its complete two-ended L1 jump retains every original-prime
Fourier mode, each nonzero. These identities construct the primitive and
preserve its full source boundary; they give no vanishing law for the fixed
physical reader.
-/

open MeasureTheory Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The original damping-two source has a complete nonzero Green jump at every prime mode. -/
theorem deningerDampingTwo_originalGreenJump_coefficient_ne_zero (p : Nat.Primes) (k : ℤ) :
    fourierCoeffOn (Real.log_pos (show (1 : ℝ)<(p : ℕ) by exact_mod_cast p.property.one_lt))
      (deningerL1OriginalBoundaryJump deningerDampingTwo_source_endpoint_integrable.1
        (Real.log (p : ℕ))) k ≠ 0 := by
  rw [deningerL1OriginalBoundaryJump_coefficient]
  exact smul_ne_zero
    (one_div_ne_zero (Real.log_pos (show (1 : ℝ)<(p : ℕ) by exact_mod_cast p.property.one_lt)).ne')
    (deningerDampingTwo_source_fourier_ne_zero _)

/-- Both ends of the same actual source converge to its nonzero original boundary. -/
theorem deningerDampingTwo_originalGreen_complete_jump (p : Nat.Primes) :
    Tendsto (fun n : ℕ =>
      deningerL1OriginalGreenCell deningerDampingTwo_source_endpoint_integrable.1
        (Real.log (p : ℕ)) (-n) -
      deningerL1OriginalGreenCell deningerDampingTwo_source_endpoint_integrable.1
        (Real.log (p : ℕ)) n) atTop
      (𝓝 (deningerL1OriginalBoundaryJump deningerDampingTwo_source_endpoint_integrable.1
        (Real.log (p : ℕ)))) :=
  deningerL1OriginalGreenCell_complete_jump _
    (Real.log_pos (show (1 : ℝ)<(p : ℕ) by exact_mod_cast p.property.one_lt))

end RHTower
