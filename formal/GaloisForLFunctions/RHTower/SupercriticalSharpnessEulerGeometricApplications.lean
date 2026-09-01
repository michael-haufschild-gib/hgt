import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFockLocal

/-!
# Sprinkling identities for Euler geometric exponents

Closed exact specializations of the sprinkling mechanism from arXiv:2603.03257.
-/

namespace RHTower

/-- Pointwise half-to-quarter sprinkling for the normalized geometric Euler exponent law. -/
theorem dyadicEulerGeometricProbability_quarter_eq_sprinkled_half (k : ℕ) :
    dyadicEulerGeometricProbability (1 / 4) k =
      (3 / 2) * (1 / 2) ^ k * dyadicEulerGeometricProbability (1 / 2) k := by
  have hpow : (1 / 4 : ℝ) ^ k = (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  rw [dyadicEulerGeometricProbability, dyadicEulerGeometricProbability, hpow]
  ring

/-- Removing the parity bit from a half-discount Euler exponent produces exactly the
quarter-discount geometric law, so the residual exponent is the sprinkled law. -/
theorem dyadicEulerResidualProbability_half_eq_quarter (j : ℕ) :
    dyadicEulerResidualProbability (1 / 2) j =
      dyadicEulerGeometricProbability (1 / 4) j := by
  unfold dyadicEulerResidualProbability
  congr 1
  norm_num

end RHTower
