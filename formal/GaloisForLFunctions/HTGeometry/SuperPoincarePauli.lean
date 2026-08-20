import GaloisForLFunctions.HTGeometry.AnticommutingPauliCarrierExponential
import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra

/-!
# Super-Poincare certificate for every phase-free Pauli word

The existing matrix representation proves every raw Pauli word is an involution.  Therefore every
word, at every qubit count, is an unconditional `N = 1` supercharge with unit translation.
-/

noncomputable section

namespace Quantum

/-- Every phase-free Pauli word is a unit-momentum `N = 1` representation. -/
def pauliWordD1N1 {n : ℕ} (p : NQubitPauliOperator n) :
    SuperPoincare.D1N1 (Matrix (NQubitBasis n) (NQubitBasis n) ℂ) where
  supercharge := p.toMatrix
  momentum := 1
  supercharge_sq := toMatrix_mul_self p

end Quantum
