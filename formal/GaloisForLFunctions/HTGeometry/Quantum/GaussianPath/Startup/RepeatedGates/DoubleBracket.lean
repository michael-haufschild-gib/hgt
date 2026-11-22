import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.SpinRelations

/-! # A nonzero second-order signal from two Pauli terms -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
noncomputable section
variable {R : Type*} [Ring R]

/-- The unscaled bracket of a Heisenberg probe with the Hamiltonian. -/
def bracket (A H : R) := A*H-H*A

/-- The second Heisenberg coefficient tested against another probe. -/
def signal₂ (A B H : R) := bracket (bracket (bracket A H) H) B

/-- If the first term anticommutes with A and the second commutes with A
but anticommutes with the first term, their mixed second-order signal is
eight times a Pauli product. The diagonal contribution commutes with B. -/
theorem double_bracket_of_paulis (A B X Y : R) (hx : X*X=1)
    (ha : X*A=-(A*X)) (hay : Commute A Y) (hxy : Y*X=-(X*Y)) (hab : Commute A B)
    (hs : B*(A*X*Y)=-(A*X*Y*B)) :
    signal₂ A B (X+Y)=8*(A*X*Y*B) := by
  have h₁ : bracket A (X+Y)=2*(A*X) := by
    simp only [bracket,mul_add,add_mul,ha,hay.eq]; noncomm_ring
  have h₂ : X*(A*X)= -A := by rw [←mul_assoc,ha,neg_mul,mul_assoc,hx,mul_one]
  have h₃ : Y*(A*X)=-(A*X*Y) := by
    rw [←mul_assoc,hay.symm.eq,mul_assoc,hxy,mul_neg,mul_assoc]
  have h₄ : bracket (bracket A (X+Y)) (X+Y)=4*A+4*(A*X*Y) := by
    rw [h₁]
    have e : bracket (2*(A*X)) (X+Y)=2*((A*X)*X+(A*X)*Y-X*(A*X)-Y*(A*X)) := by
      dsimp only [bracket]; noncomm_ring
    rw [e,h₂,h₃,mul_assoc A X X,hx,mul_one]
    noncomm_ring
  rw [signal₂,h₄,bracket]
  calc _ = 4*(A*B-B*A)+4*(A*X*Y*B-B*(A*X*Y)) := by noncomm_ring
       _ = _ := by rw [hab.eq,hs]; noncomm_ring

end
end GaloisForLFunctions.HTGeometry.RepeatedGates
