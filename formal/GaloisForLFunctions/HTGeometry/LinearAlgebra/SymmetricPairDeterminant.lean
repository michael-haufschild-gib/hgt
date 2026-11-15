import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingSchur
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Determinants under a skew-pair perturbation

For a symmetric matrix, a skew pair supported on two coordinates changes the
determinant by the square of its parameter times the complementary principal
minor. No invertibility is required: row multilinearity and symmetry of the
adjugate cancel the two linear terms. Over the binary field, summing the two
parameter choices deletes the matched pair.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Simultaneous changes in two distinct rows have four multilinear terms. -/
theorem det_twoRow_add (M : Matrix n n R) (i j : n) (hij : i ≠ j) (u v : n → R) :
    ((M.updateRow i (M i + u)).updateRow j (M j + v)).det =
      M.det + (M.updateRow i u).det + (M.updateRow j v).det +
        ((M.updateRow i u).updateRow j v).det := by
  have hi := updateRow_eq_self M i
  have hj := updateRow_eq_self M j
  have hfirst : (M.updateRow i (M i + u)).updateRow j (M j) =
      M.updateRow i (M i + u) := by
    rw [updateRow_comm M hij, hj]
  have hsecond : ((M.updateRow i (M i + u)).updateRow j v).det =
      (M.updateRow j v).det + ((M.updateRow i u).updateRow j v).det := by
    rw [updateRow_comm M hij, det_updateRow_add,
      ← updateRow_comm M hij (M i) v, hi, ← updateRow_comm M hij u v]
  rw [det_updateRow_add, hfirst, det_updateRow_add, hi, hsecond]
  abel

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A skew pair at the final two coordinates is a pair of opposite row increments. -/
theorem pairBorder_eq_twoRow_update (M : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) F) (t : F) :
    M + fromBlocks (0 : Matrix ι ι F) 0 0 (alternatingPair t) =
      (M.updateRow (Sum.inr 0) (M (Sum.inr 0) + t • Pi.single (Sum.inr 1) 1)).updateRow
        (Sum.inr 1) (M (Sum.inr 1) + (-t) • Pi.single (Sum.inr 0) 1) := by
  ext (i | i) (j | j)
  · simp [Matrix.updateRow, fromBlocks]
  · fin_cases j <;> simp [Matrix.updateRow, fromBlocks]
  · fin_cases i <;> simp [Matrix.updateRow, fromBlocks]
  · fin_cases i <;> fin_cases j <;>
      simp [Matrix.updateRow, fromBlocks, alternatingPair]

/-- Replacing the two border rows by the skew pair leaves a triangular block matrix. -/
theorem det_pairBorder_basisRows (M : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) F) (t : F) :
    ((M.updateRow (Sum.inr 0) (t • Pi.single (Sum.inr 1) 1)).updateRow
      (Sum.inr 1) ((-t) • Pi.single (Sum.inr 0) 1)).det = t ^ 2 * M.toBlocks₁₁.det := by
  have hblocks : (M.updateRow (Sum.inr 0) (t • Pi.single (Sum.inr 1) 1)).updateRow
      (Sum.inr 1) ((-t) • Pi.single (Sum.inr 0) 1) =
      fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 (alternatingPair t) := by
    ext (i | i) (j | j)
    · simp [Matrix.updateRow, fromBlocks, toBlocks₁₁]
    · fin_cases j <;> simp [Matrix.updateRow, fromBlocks, toBlocks₁₂]
    · fin_cases i <;> simp [Matrix.updateRow, fromBlocks]
    · fin_cases i <;> fin_cases j <;>
        simp [Matrix.updateRow, fromBlocks, alternatingPair]
  have hp : (alternatingPair t).det = t ^ 2 := by
    simp [alternatingPair, det_fin_two, pow_two]
  rw [hblocks, det_fromBlocks_zero₂₁, hp, mul_comm]

/-- A skew-pair perturbation of a symmetric matrix has no linear determinant term.
Its quadratic coefficient is the complementary principal minor, including singular matrices. -/
theorem det_symmetric_pairBorder (M : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) F)
    (hM : M.IsSymm) (t : F) :
    (M + fromBlocks (0 : Matrix ι ι F) 0 0 (alternatingPair t)).det =
      M.det + t ^ 2 * M.toBlocks₁₁.det := by
  have hij : (Sum.inr 0 : ι ⊕ Fin 2) ≠ Sum.inr 1 := by simp
  have hc : M.adjugate (Sum.inr 1) (Sum.inr 0) =
      M.adjugate (Sum.inr 0) (Sum.inr 1) := by
    have hsym : M.adjugateᵀ = M.adjugate := by rw [adjugate_transpose, hM]
    exact congrArg (fun N : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) F =>
      N (Sum.inr 0) (Sum.inr 1)) hsym
  have hu : (M.updateRow (Sum.inr 0) (t • Pi.single (Sum.inr 1) 1)).det =
      t * M.adjugate (Sum.inr 1) (Sum.inr 0) := by
    rw [det_updateRow_smul, ← adjugate_apply]
  have hv : (M.updateRow (Sum.inr 1) ((-t) • Pi.single (Sum.inr 0) 1)).det =
      (-t) * M.adjugate (Sum.inr 0) (Sum.inr 1) := by
    rw [det_updateRow_smul, ← adjugate_apply]
  rw [pairBorder_eq_twoRow_update, det_twoRow_add _ _ _ hij,
    hu, hv, det_pairBorder_basisRows, hc]
  ring

/-- Summing the two binary choices deletes the final matched pair from the determinant. -/
theorem binary_pairBorder_det_sum (M : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) (ZMod 2))
    (hM : M.IsSymm) :
    M.det + (M + fromBlocks (0 : Matrix ι ι (ZMod 2)) 0 0 (alternatingPair 1)).det =
      M.toBlocks₁₁.det := by
  rw [det_symmetric_pairBorder M hM, one_pow, one_mul, ← add_assoc,
    CharTwo.add_self_eq_zero, zero_add]

#print axioms det_twoRow_add
#print axioms det_symmetric_pairBorder
#print axioms binary_pairBorder_det_sum
end GaloisForLFunctions.HTGeometry.LinearAlgebra
