/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import GaloisForLFunctions.QuantumAlg.Primitives.SwapTest

/-!
# Symmetric two-strand braid action

The register swap realizes the symmetric braiding on two equal quantum registers.  It satisfies the
two-strand Reidemeister-II cancellation relation on decomposable states.  Because positive and
negative crossings have identical action, this factors through the symmetric group and does not
provide a Jones-polynomial braid representation.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- The elementary crossings of a two-strand oriented braid word. -/
inductive TwoStrandCrossing where
  | positive
  | negative
  deriving DecidableEq

/-- Symmetric braiding action: both crossings act by register exchange. -/
def symmetricCrossingAction (n : ℕ) : TwoStrandCrossing → Gate (Qubits (n + n))
  | .positive => swapRegisters n
  | .negative => swapRegisters n

theorem symmetricCrossingAction_positive (n : ℕ) :
    symmetricCrossingAction n .positive = swapRegisters n := rfl

theorem symmetricCrossingAction_negative (n : ℕ) :
    symmetricCrossingAction n .negative = swapRegisters n := rfl

/-- Reidemeister-II cancellation on decomposable states for the symmetric braiding. -/
theorem symmetric_braid_reidemeister_II (psi phi : PureState (Qubits n)) :
    (symmetricCrossingAction n .positive * symmetricCrossingAction n .negative).apply
      (psi.tensor phi) = psi.tensor phi := by
  rw [symmetricCrossingAction_positive, symmetricCrossingAction_negative, Gate.mul_apply,
    swapRegisters_apply_tensor, swapRegisters_apply_tensor]

end

end QuantumAlg
