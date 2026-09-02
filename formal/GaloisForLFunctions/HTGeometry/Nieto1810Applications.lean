import GaloisForLFunctions.HTGeometry.Nieto1810GrassmannPlucker
import GaloisForLFunctions.HTGeometry.Nieto1810EpsilonDuality
import GaloisForLFunctions.HTGeometry.Nieto1810Gonshor

/-!
# Applications of arXiv:1810.04521 across the Lean corpus

Umbrella for unconditional mechanical transfers involving Grassmann--Pluecker coordinates,
qubit flattenings, twistors, null spinors, epsilon parity, and finite Gonshor sign strings.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.Nieto1810

/-- The local epsilon sign is the complexification of the corpus's Euler--Wick gauge sign. -/
theorem epsilonBitSign_eq_binaryGaugeSign (b : Fin 2) :
    epsilonBitSign b = (RHTower.binaryGaugeSign (finBitBool b) : ℂ) := by
  fin_cases b <;>
    norm_num [epsilonBitSign, finBitBool, RHTower.binaryGaugeSign]

/-- Epsilon-tensor parity is literally the full Walsh character of the same bitstring. -/
theorem epsilonTensorSign_eq_binaryGaugeWalshCharacter {n : ℕ}
    (a : Quantum.NQubitBasis n) :
    epsilonTensorSign a =
      (RHTower.binaryGaugeWalshCharacter
        (Finset.univ : Finset (Fin n)) (fun i => finBitBool (a i)) : ℂ) := by
  rw [epsilonTensorSign, RHTower.binaryGaugeWalshCharacter]
  push_cast
  simp only [epsilonBitSign_eq_binaryGaugeSign]

end GaloisForLFunctions.Nieto1810
