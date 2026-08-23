import Mathlib

/-!
# Cesàro dephasing is not irreversible information loss

A Cesàro mean can converge to a positive dephasing defect without being the
loss history of any time-homogeneous contractive observer.  The smallest
two-phase packet already exhibits information backflow: its deficit rises
from time two to two units and then falls at time three to `4/3`.

This is a design constraint for completion-error dynamics.  A collision
charge recovered by Cesàro dephasing cannot be inserted into an irreversible
action ledger until a separate Markov/observer realization proves monotone
data processing on the same clock.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Coherent amplitude of the two unit phases `1` and `-1`. -/
def parityCoherentAmplitude (c : ℕ) : ℂ :=
  1 + (-1 : ℂ) ^ c

/-- Resolved energy of the parity packet. -/
def parityResolvedEnergy (c : ℕ) : ℝ :=
  ‖parityCoherentAmplitude c‖ ^ 2

/-- Deficit of the finite Cesàro-resolved energy from its coherent value. -/
def parityCesaroInformationLoss (M : ℕ) : ℝ :=
  4 - (M : ℝ)⁻¹ * ∑ c ∈ Finset.range M, parityResolvedEnergy c

theorem parityCesaroInformationLoss_one :
    parityCesaroInformationLoss 1 = 0 := by
  norm_num [parityCesaroInformationLoss, parityResolvedEnergy,
    parityCoherentAmplitude, Complex.norm_real]

theorem parityCesaroInformationLoss_two :
    parityCesaroInformationLoss 2 = 2 := by
  norm_num [parityCesaroInformationLoss, parityResolvedEnergy,
    parityCoherentAmplitude, Complex.norm_real, Finset.sum_range_succ]

theorem parityCesaroInformationLoss_three :
    parityCesaroInformationLoss 3 = 4 / 3 := by
  norm_num [parityCesaroInformationLoss, parityResolvedEnergy,
    parityCoherentAmplitude, Complex.norm_real, Finset.sum_range_succ]

/-- A positive Cesàro dephasing defect is not, merely from its construction,
an irreversible observer loss: even the two-phase deficit has backflow. -/
theorem parityCesaroInformationLoss_not_monotone :
    ¬ Monotone parityCesaroInformationLoss := by
  intro hmono
  have h := hmono (show 2 ≤ 3 by norm_num)
  norm_num [parityCesaroInformationLoss, parityResolvedEnergy,
    parityCoherentAmplitude, Complex.norm_real, Finset.sum_range_succ] at h

end GaloisForLFunctions.HTGeometry
