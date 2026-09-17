import GaloisForLFunctions.RHTower.SPEQuantileRieszParabolicBridge

/-!
# Physical-wall gauge decomposition of the completed SP-E parabolic current

The completed SP-E Riesz observable is not the canonical source-centred parabolic charge.  It is
the pairing with a moving covector fixed by the physical aperture wall.  This module identifies
the exact change-of-gauge obstruction without introducing a surrogate bound: after multiplying
by the literal completed source mass, the Riesz readout splits into the terminal-aware cross-cell
source current, a physical-wall/source-barycentre transport term, and the oriented terminal mass
mismatch.  All three terms remain literal.

This is a structural reduction, not an RH estimate.  In particular, controlling only the
source-centred strict-cross pairing cannot control the SP-E observable unless the two retained
gauge terms are controlled as well.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The covector selected by the literal SP-E physical wall at integer aperture `M`. -/
def speQuantileRieszPhysicalWallCovector (M : ℕ) : Fin 3 → ℝ :=
  ![-1, -Real.sqrt (M : ℝ), 0]

/-- The SP-E parabolic Riesz readout is exactly pairing with its physical-wall covector. -/
theorem speQuantileRieszParabolicReadout_eq_pairing_physicalWallCovector
    (M : ℕ) (v : Fin 3 → ℝ) :
    speQuantileRieszParabolicReadout M v =
      ccmParabolicPairing v (speQuantileRieszPhysicalWallCovector M) := by
  simp [speQuantileRieszParabolicReadout, ccmParabolicPairing,
    speQuantileRieszPhysicalWallCovector]
  ring

/-- Multiplying a physical-wall Riesz readout by any boundary mass isolates its complete
parabolic pairing, its barycentric gauge mismatch, and its mass mismatch.  No division or
nonvanishing assumption is used. -/
theorem mul_speQuantileRieszParabolicReadout_eq_neg_pairing_add_gaugeResidual
    (M : ℕ) (v b : Fin 3 → ℝ) :
    b 0 * speQuantileRieszParabolicReadout M v =
      -ccmParabolicPairing v b +
        (Real.sqrt (M : ℝ) * b 0 - b 1) * v 1 + b 2 * v 0 := by
  simp [speQuantileRieszParabolicReadout, ccmParabolicPairing]
  ring

/-- In the gauge translated by the physical wall, the Riesz readout is the negative second
coordinate plus its forced mass correction. -/
theorem speQuantileRieszParabolicReadout_eq_physicalShift
    (M : ℕ) (v : Fin 3 → ℝ) :
    speQuantileRieszParabolicReadout M v =
      -(ccmParabolicShift (-Real.sqrt (M : ℝ)) v 2) + (M : ℝ) / 2 * v 0 := by
  simp [speQuantileRieszParabolicReadout, ccmParabolicShift]
  ring

/-- **Physical-wall/source decomposition.** For the literal terminal-completed codiagonal at
the SP-E aperture, its Riesz current consists exactly of the terminal-aware source pairing, the
physical-wall/source-barycentre mismatch times the first codiagonal coordinate, and the oriented
terminal mass mismatch.  This keeps the two terms which source centering alone cannot erase. -/
theorem completedParabolic_physicalWall_sourceBoundary_decomposition
    (M : ℕ) :
    let C := ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal
      (M - 3) (Real.log M)
    let B := ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary
      (M - 3) (Real.log M)
    B 0 * speQuantileRieszParabolicReadout M C =
      -ccmParabolicPairing C B +
        (Real.sqrt (M : ℝ) * B 0 - B 1) * C 1 + B 2 * C 0 := by
  dsimp only
  exact mul_speQuantileRieszParabolicReadout_eq_neg_pairing_add_gaugeResidual M _ _

/-- The source-pairing term in the physical-wall decomposition is exactly the finite strict-cross
current less the full literal terminal interaction.  Therefore the decomposition retains both
cross-prime orientation and the terminal form. -/
theorem completedParabolic_physicalWall_decomposition_eq_finiteCross_sub_terminal
    (M : ℕ) :
    let K := M - 3
    let T := Real.log M
    let C := ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T
    let B := ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T
    B 0 * speQuantileRieszParabolicReadout M C =
      -(ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) -
        (2 * ccmParabolicPairing (ccmActualHeadQuantileParabolicAggregate K)
            (ccmActualHeadQuantileParabolicTerminal K T) +
          ccmParabolicForm (ccmActualHeadQuantileParabolicTerminal K T))) +
        (Real.sqrt (M : ℝ) * B 0 - B 1) * C 1 + B 2 * C 0 := by
  dsimp only
  rw [completedParabolic_physicalWall_sourceBoundary_decomposition,
    ccmActualHeadMatchedCompletedQuantileParabolic_pairing_eq_finite_sub_terminal]

end RHTower
