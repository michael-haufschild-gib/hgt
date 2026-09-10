import GaloisForLFunctions.HTGeometry.GomesFockInvariantForms
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# The actual finite Fock derivative has a cyclic top jet

Every power of the existing derivative clock has an exact coordinate formula.
Its highest jet generates every coordinate vector. Consequently a commuting
matrix is determined by its action on that one jet, without further assumptions.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The full symmetry algebra of the literal finite Fock derivative clock. -/
def gomesFiniteFockCommutant (N : ℕ) : Subalgebra ℂ (Matrix (Fin N) (Fin N) ℂ) :=
  Subalgebra.centralizer ℂ {fockShiftMatrix N}

/-- Membership means commutation with the existing derivative matrix. -/
theorem gomesFiniteFockCommutant_mem_iff (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) :
    M ∈ gomesFiniteFockCommutant N ↔ Commute M (fockShiftMatrix N) := by
  simp only [gomesFiniteFockCommutant, Subalgebra.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  exact eq_comm

/-- Powers move precisely along the appropriate superdiagonal, in every dimension. -/
theorem gomesFiniteFockShift_pow_apply (N k : ℕ) (i j : Fin N) :
    (fockShiftMatrix N ^ k) i j = if i.val + k = j.val then 1 else 0 := by
  rw [← fockMatrix_mulVec_coord (fockShiftMatrix N ^ k) j i,
    fockShiftMatrix_pow_mulVec, shiftOp_iterate_apply]
  exact jetExt_coordVec j.isLt _

/-- The highest jet is cyclic: a suitable clock power yields every coordinate jet. -/
theorem gomesFiniteFockShift_top_cyclic (n : ℕ) (i : Fin (n + 1)) :
    fockShiftMatrix (n + 1) ^ (n - i.val) *ᵥ coordVec n = coordVec i.val := by
  rw [fockShiftMatrix_pow_mulVec]
  funext j
  rw [shiftOp_iterate_apply, jetExt_coordVec (Nat.lt_succ_self n)]
  change (if j.val + (n - i.val) = n then (1 : ℂ) else 0) =
    if j.val = i.val then 1 else 0
  have he : j.val + (n - i.val) = n ↔ j.val = i.val := by
    constructor
    · intro h
      exact Nat.add_right_cancel (h.trans (Nat.add_sub_of_le i.is_le).symm)
    · intro h
      rw [h, Nat.add_sub_of_le i.is_le]
  simp only [he]

/-- One top-jet observation determines every actual commuting matrix. -/
theorem gomesFiniteFockCommutant_top_injective (n : ℕ) :
    Function.Injective (fun E : gomesFiniteFockCommutant (n + 1) =>
      E.val *ᵥ coordVec n) := by
  intro E F h
  change E.val *ᵥ coordVec n = F.val *ᵥ coordVec n at h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hE := (gomesFiniteFockCommutant_mem_iff _ E.val).mp E.property
  have hF := (gomesFiniteFockCommutant_mem_iff _ F.val).mp F.property
  rw [← fockMatrix_mulVec_coord E.val j i, ← fockMatrix_mulVec_coord F.val j i,
    ← gomesFiniteFockShift_top_cyclic n j, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, (hE.pow_right _).eq, (hF.pow_right _).eq,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
