import GaloisForLFunctions.HTGeometry.GreedyBumpFiniteClockApplications
import GaloisForLFunctions.RHTower.SoninLogClockQuantumFisher

/-!
# Greedy-bump profiling for the logarithmic Sonin clock

The involutive-clock application is specialized to the corpus's physical
Sonin sector.  Physicality supplies stationarity; normalization is data.
-/

open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized physical Sonin state and observed operator. -/
structure GreedyBumpSoninClockData where
  observable : SoninL2 →L[ℂ] SoninL2
  state : SoninL2
  stateNorm : ‖state‖ = 1
  physical : GaloisForLFunctions.PhysicalState
    (soninLogFourierScattering - 1).toLinearMap state

/-- Physical Sonin data as an admissible two-reading clock. -/
def GreedyBumpSoninClockData.toInvolutiveClock
    (A : GreedyBumpSoninClockData) : GreedyBumpInvolutiveClockData SoninL2 where
  evolution := soninLogFourierScattering
  observable := A.observable
  isometry := soninLogFourierScattering_adjoint_mul_self
  involutive := soninLogFourierScattering_sq_eq_one
  state := A.state
  state_norm := A.stateNorm
  state_fixed := by
    have h := A.physical
    rw [GaloisForLFunctions.PhysicalState] at h
    apply sub_eq_zero.mp
    simpa using h

/-- Sonin greedy-profile gain is scattering-commutator energy divided by `8Q`. -/
theorem greedyBump_soninClock_profileGain_eq_commutator
    (A : GreedyBumpSoninClockData) (Q : PositiveSignal) :
    greedyBumpProfile Q A.toInvolutiveClock.toFiniteClock.erasedTangent
        (greedyBumpDisplacement Q A.toInvolutiveClock.toFiniteClock.erasedTangent) =
      ‖((A.observable * soninLogFourierScattering -
        soninLogFourierScattering * A.observable) :
        SoninL2 →L[ℂ] SoninL2) A.state‖ ^ (2 : ℕ) / (8 * (Q : ℝ)) := by
  simpa [GreedyBumpSoninClockData.toInvolutiveClock] using
    greedyBump_involutiveClock_profileGain_eq_commutator
      A.toInvolutiveClock Q

/-- Equivalent Sonin dephasing law with the double scattering commutator. -/
theorem greedyBump_soninClock_profileGain_eq_doubleCommutator
    (A : GreedyBumpSoninClockData) (Q : PositiveSignal) :
    greedyBumpProfile Q A.toInvolutiveClock.toFiniteClock.erasedTangent
        (greedyBumpDisplacement Q A.toInvolutiveClock.toFiniteClock.erasedTangent) =
      ‖soninLogFourierDoubleCommutator A.observable A.state‖ ^ (2 : ℕ) /
        (32 * (Q : ℝ)) := by
  simpa [GreedyBumpSoninClockData.toInvolutiveClock,
    soninLogFourierDoubleCommutator] using
    greedyBump_involutiveClock_profileGain_eq_doubleCommutator
      A.toInvolutiveClock Q

end

end RHTower
