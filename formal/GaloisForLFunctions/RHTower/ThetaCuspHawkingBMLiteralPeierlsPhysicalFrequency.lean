import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamFrequencyDefectCochain
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralPeierlsStreamBilinear

/-!
# Physical-frequency literal cyclic Peierls bulk equation

The off-frequency two-leg metric has one explicit source-pole cochain.  At
the physical frequency this factor vanishes.  This module identifies that
specialization with the original literal stream bilinear field and derives its
unconditional, componentwise cosmological Einstein equation with the paired
physical source.

Proof-chain role:
`literal two-leg bulk equation -> causal retarded-minus-advanced realization
and cap/contact pairing -> cyclic Peierls incidence -> HB causal-cut test`.
The causal and noncompact boundary steps are deliberately not asserted here.
-/

namespace RHTower.D4BMLiteralPeierlsPhysicalFrequency

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMFundamentalScalarMetric D4BMModularCore
open D4BMLiteralPeierlsStream
open ComplexCoordinateMetricTwoJet

noncomputable section
set_option autoImplicit false

private theorem frequencyStreamMetricField_physical (w a : ℂ) (square : Bool)
    (V : Covector) (x : Fin 4 → ℝ) :
    frequencyStreamMetricField w w a square V x = streamMetricField w a square V x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frequencyStreamMetricField, streamMetricField, frequencyStreamTimeBlock,
      frequencyStreamRadiusBlock, frequencyRadialField, frequencyRadialDerivative,
      frequencyPhase, streamTimeBlock, streamRadiusBlock]

/-- At physical frequency the source-pole bilinear metric is exactly the
original literal stream polarization. -/
theorem frequencyMixedMetricBilinear_physical (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (x : Fin 4 → ℝ) :
    frequencyMixedMetricBilinear q branch (2 * physicalRate q branch) a d x =
      forcedMetricBilinear q branch a d x := by
  change
    frequencyStreamMetricBilinear (2 * physicalRate q branch)
        (2 * physicalRate q branch) false (fullAngularCovector q branch) a d x -
      (physicalRate q branch * (physicalRate q branch - 1) / 4) •
        frequencyStreamMetricBilinear (2 * physicalRate q branch)
          (2 * physicalRate q branch) true (fullSquareCovector q) a d x =
      streamMetricBilinear (2 * physicalRate q branch) false
          (fullAngularCovector q branch) a d x -
        (physicalRate q branch * (physicalRate q branch - 1) / 4) •
          streamMetricBilinear (2 * physicalRate q branch) true
            (fullSquareCovector q) a d x
  simp only [frequencyStreamMetricBilinear, streamMetricBilinear, LinearMap.mk₂_apply]
  rw [frequencyStreamMetricField_physical, frequencyStreamMetricField_physical]

/-- At physical frequency the two independent primary legs produce precisely
the original paired Einstein source. -/
theorem frequencyMixedSourceBilinear_physical (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (x : Fin 4 → ℝ) :
    frequencyMixedSourceBilinear q branch (2 * physicalRate q branch) a d x =
      literalMixedSourceBilinear q branch (x 1)
        (envelope (physicalRate q branch) a x)
        (envelope (physicalRate q branch) d x) (angularPoint x) := by
  unfold frequencyMixedSourceBilinear
  have hrate : (2 * physicalRate q branch) / 2 = physicalRate q branch := by ring
  rw [hrate, frequencyEnvelope_diagonal, frequencyEnvelope_diagonal]

/-- Literal cyclic Peierls bulk realization at the physical frequency: the
actual polarized stream field solves every exterior cosmological Einstein
component against its two-leg physical mixed source. -/
theorem forcedMetricBilinear_cosmological_source (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (a d : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (forcedMetricBilinear q branch a d) p.val) (-3) i j +
      literalMixedSourceBilinear q branch (p.val 1)
        (envelope (physicalRate q branch) a p.val)
        (envelope (physicalRate q branch) d p.val) (angularPoint p.val) i j = 0 := by
  have h := frequencyMixedMetricBilinear_cosmological_source q branch p
    (2 * physicalRate q branch) a d i j
  rw [frequencyMixedMetricBilinear_physical, frequencyMixedSourceBilinear_physical] at h
  simpa using h

end

end RHTower.D4BMLiteralPeierlsPhysicalFrequency
