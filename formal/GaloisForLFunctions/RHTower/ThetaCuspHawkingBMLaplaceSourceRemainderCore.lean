import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerCore

/-! The literal undressed radial source remainder, independent of current transport. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

/-- Literal undressed source density in the true compact radial coordinate. -/
def sourceRemainder (s w a J K T : ℂ) (z : ℝ) : ℂ :=
  power (2 * s - w) (1 + Real.sqrt (1 - z)) * a ^ (2 : ℕ) *
    (((5 * s ^ (2 : ℕ) + 15 * s + 4) / 4) * J +
      (1 - (z : ℂ)) * s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)) * T

end
end RHTower.D4BMLaplaceRadial
