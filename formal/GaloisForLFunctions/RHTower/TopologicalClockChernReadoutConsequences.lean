import GaloisForLFunctions.RHTower.TopologicalClockDynamicsBridges
import GaloisForLFunctions.RHTower.TopologicalClockWindingReadout
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.KnotChernSimonsBridge

/-!
# Operational Chern consequences of topological clock readout

This module packages the phase-jump and Dirac-mass winding coordinates used by
arXiv:2608.27650.  `phaseJumpChern` is the paper's operational Berry-phase endpoint coordinate;
it is not a replacement for a general two-dimensional vector-bundle Chern class.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.TopologicalClockApplications

/-- Chern coordinate extracted from a lifted Berry-phase endpoint jump. -/
def phaseJumpChern (phase : ℝ → ℝ) : ℝ :=
  -(phase Real.pi - phase (-Real.pi)) / (2 * Real.pi)

theorem phaseJumpChern_linearGeometricPhase (C : ℤ) :
    phaseJumpChern (linearGeometricPhase C) = (C : ℝ) := by
  rw [phaseJumpChern, linearGeometricPhase_endpoint_jump]
  field_simp [Real.pi_ne_zero]

theorem phaseJumpChern_periodicResidual (C : ℤ) (a b c : ℝ) :
    phaseJumpChern (phaseWithPeriodicResidual C a b c) = (C : ℝ) := by
  rw [phaseJumpChern, periodicResidual_preserves_endpoint_jump]
  field_simp [Real.pi_ne_zero]

/-- Dirac-mass winding coordinate of the normalized Rice--Mele pump. -/
def riceMelePumpChern : ℤ :=
  PrimeQuasiLocalCharge.scalarCircleLoopWinding riceMeleDiracMassLoop

theorem riceMelePumpChern_eq_one : riceMelePumpChern = 1 := by
  exact riceMeleDiracMassLoop_winding

theorem riceMele_phaseJumpChern_eq_one :
    phaseJumpChern (linearGeometricPhase riceMelePumpChern) = 1 := by
  rw [phaseJumpChern_linearGeometricPhase, riceMelePumpChern_eq_one]
  norm_num

theorem riceMele_readout_winding_eq_neg_two_chern :
    RHTower.windingNumber
        (fun t => paperGeometricLoop riceMelePumpChern t ^ 2)
        0 (2 * Real.pi) = -2 * riceMelePumpChern := by
  exact paperForwardBackwardReadout_winding riceMelePumpChern

theorem riceMele_readout_winding_eq_neg_two :
    RHTower.windingNumber
        (fun t => paperGeometricLoop riceMelePumpChern t ^ 2)
        0 (2 * Real.pi) = -2 := by
  rw [riceMele_readout_winding_eq_neg_two_chern, riceMelePumpChern_eq_one]
  norm_num

theorem z2ChernSimonsLinkPhase_clockReadout_trivial (linking : ZMod 2) :
    Quantum.Stabilizer.Lattice.z2ChernSimonsLinkPhase linking ^ 2 = 1 := by
  unfold Quantum.Stabilizer.Lattice.z2ChernSimonsLinkPhase
  split <;> norm_num

theorem fundamentalToricLink_clockReadout_trivial :
    Quantum.Stabilizer.Lattice.z2ChernSimonsLinkPhase
        (Quantum.Stabilizer.Lattice.toricChernSimonsLinking
          Quantum.Stabilizer.Lattice.toricHorizontalWilsonLoop
          Quantum.Stabilizer.Lattice.toricVerticalWilsonLoop) ^ 2 = 1 := by
  exact z2ChernSimonsLinkPhase_clockReadout_trivial _

/-- Integer `K₁` readout is injective although the same squaring protocol erases every `Z₂` phase. -/
theorem integerKOne_injective_toricZ2_erased :
    Function.Injective PrimeQuasiLocalCharge.topologicalClockReadoutKOne ∧
      ∀ linking : ZMod 2,
        Quantum.Stabilizer.Lattice.z2ChernSimonsLinkPhase linking ^ 2 = 1 := by
  exact ⟨PrimeQuasiLocalCharge.topologicalClockReadoutKOne_injective,
    z2ChernSimonsLinkPhase_clockReadout_trivial⟩

end GaloisForLFunctions.RHTower.TopologicalClockApplications

end
