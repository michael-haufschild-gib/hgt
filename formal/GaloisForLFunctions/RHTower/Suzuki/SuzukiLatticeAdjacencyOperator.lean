import GaloisForLFunctions.HTGeometry.LatticeL2Shift
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLatticePositionCommutator

/-!
# The finite-range lattice adjacency as a bounded `ℓ²` operator

Each translation is an isometry of `ℓ²`, so a finite real combination of them is a bounded operator;
symmetry of the step set and of the coefficients makes it self-adjoint.  Its action on the
underlying field is the finite-range adjacency of the position-commutator module, so the exact
commutator identity `(16)` transfers verbatim to the operator.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

/-- The translation as a continuous linear map. -/
def latticeShiftCLM (q : P → ℤ) : H →L[ℂ] H :=
  (GaloisForLFunctions.HTGeometry.latticeShift q).toLinearIsometry.toContinuousLinearMap

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem latticeShiftCLM_apply (q : P → ℤ) (ψ : H) (ν : P → ℤ) :
    ((latticeShiftCLM q ψ : H) : (P → ℤ) → ℂ) ν = (ψ : (P → ℤ) → ℂ) (ν + q) := rfl

/-- The finite-range lattice adjacency as a bounded operator. -/
def latticeAdjacency (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) : H →L[ℂ] H :=
  ∑ q ∈ Q, c q • latticeShiftCLM q

omit [Fintype P] [DecidableEq P] in
theorem latticeAdjacency_apply (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (ψ : H) (ν : P → ℤ) :
    ((latticeAdjacency Q c ψ : H) : (P → ℤ) → ℂ) ν
      = adjacencyField Q c (ψ : (P → ℤ) → ℂ) ν := by
  rw [latticeAdjacency, adjacencyField]
  rw [_root_.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hsmul : ((c q • latticeShiftCLM q) ψ : H) = c q • (latticeShiftCLM q ψ : H) := rfl
  rw [hsmul, lp.coeFn_smul, Pi.smul_apply, latticeShiftCLM_apply, smul_eq_mul]

omit [Fintype P] [DecidableEq P] in
theorem norm_latticeAdjacency_le (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) :
    ‖latticeAdjacency Q c‖ ≤ ∑ q ∈ Q, ‖c q‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun q _ => ?_
  rw [norm_smul]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (le_of_eq (mul_one _))
  rw [latticeShiftCLM]
  exact LinearIsometry.norm_toContinuousLinearMap_le _

end RHTower
