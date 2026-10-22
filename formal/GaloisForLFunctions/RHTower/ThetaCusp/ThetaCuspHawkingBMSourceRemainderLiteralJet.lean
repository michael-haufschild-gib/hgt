import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceSourceRemainderCore
import GaloisForLFunctions.HTGeometry.LiteralSourceAffinePowerUniformJet

/-! The literal source remainder is the affine cubic-jet factor with no data omitted. -/

namespace RHTower.D4BMLaplaceRadial
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The actual radial source remainder is exactly the affine factor whose
three-counterterm jet was proved in `HTGeometry`.  Both angular channels remain
in `B₀` and `B₁`. -/
theorem sourceRemainder_eq_literalSourceAffinePower (s w a J K T : ℂ) (z : ℝ) :
    sourceRemainder s w a J K T z =
      literalSourceAffinePower (2 * s - w)
        (((5 * s ^ (2 : ℕ) + 15 * s + 4) / 4) * J +
          s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K))
        (s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)) z * (a ^ (2 : ℕ) * T) := by
  unfold literalSourceAffinePower horizonAffinePowerCore
  rw [literalSourceHorizonPower_eq_cpow]
  unfold sourceRemainder power
  simp only [literalSourceHorizonHeight]
  ring

end
end RHTower.D4BMLaplaceRadial
