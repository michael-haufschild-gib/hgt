import GaloisForLFunctions.RHTower.QuantumGraphPrimePowerDecoupling
import Mathlib.Analysis.Complex.Basic

/-! # Principal-minor weights of a circuit in any orthonormal frame -/

open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
open RHTower.QuantumGraphPrimePowerDecoupling
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Hadamard's inequality bounds the modulus of every principal minor of
a unitary by one, including minors of intermediate exterior degrees. -/
theorem principal_weight_le (W : unitary (Matrix I I ℂ)) (S : Finset I) :
    ‖(W.val.submatrix (Subtype.val : S → I) Subtype.val).det‖≤1 := by
  let blk (i : I) := decide (i∈S)
  let e : S ≃ {j // blk j=true} := Equiv.subtypeEquivRight (by simp [blk])
  have he : (principalBlock W.val blk true).submatrix e e=
      W.val.submatrix (Subtype.val : S → I) Subtype.val := rfl
  rw [←he,det_submatrix_equiv_self]
  refine (norm_det_principalBlock_le W.val blk true).trans ?_
  refine prod_le_one (fun _ _ => Real.sqrt_nonneg _) (fun j _ => ?_)
  have h := blockColumnNorm_le_one W.2 blk j.val
  simpa only [blockColumnNorm,j.property] using h

#print axioms principal_weight_le
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
