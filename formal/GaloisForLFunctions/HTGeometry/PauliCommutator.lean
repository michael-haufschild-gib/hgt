import GaloisForLFunctions.HTGeometry.PauliProductLaw

/-!
# Commutators of Pauli strings

Two Pauli strings multiply to the same label in either order, so their commutator is the difference
of the two product phases times that label's Pauli string.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem boolPauliOption_commutator (p q : Option (Fin 3)) :
    boolPauliOption p * boolPauliOption q - boolPauliOption q * boolPauliOption p =
      (optPhase p q - optPhase q p) • boolPauliOption (optMul p q) := by
  rw [boolPauliOption_mul, boolPauliOption_mul, optMul_comm q p, sub_smul]

theorem finitePauliMatrix_commutator {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P Q : σ → Option (Fin 3)) :
    finitePauliMatrix P * finitePauliMatrix Q - finitePauliMatrix Q * finitePauliMatrix P =
      ((∏ s, optPhase (P s) (Q s)) - ∏ s, optPhase (Q s) (P s)) •
        finitePauliMatrix fun s => optMul (P s) (Q s) := by
  have hcomm : (fun s => optMul (Q s) (P s)) = fun s => optMul (P s) (Q s) := by
    funext s
    exact optMul_comm (Q s) (P s)
  rw [finitePauliMatrix_mul, finitePauliMatrix_mul, hcomm, sub_smul]

end GaloisForLFunctions.HTGeometry
