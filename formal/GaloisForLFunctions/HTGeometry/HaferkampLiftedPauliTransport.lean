import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitArchitecture
import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitPauliTransport

/-!
# Lifting local Pauli transport to an arbitrary finite qubit register

This module supplies the exact bridge from the Boolean two-qubit Clifford
transport to an arbitrary finite register.  It separates two distinguished
qubits from the remainder, factors literal finite Pauli matrices across that
split, and proves that a local `SU(4)` transport acts only on the two selected
Pauli labels.
-/

open Matrix
open scoped BigOperators Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The canonical equivalence between the two-times-removed coordinate type
and successive removal of first `a`, then `b`. -/
def twoQubitRestEquiv
    {Q : Type*} [DecidableEq Q] (a b : Q) (hab : a ≠ b) :
    {q : Q // q ≠ a ∧ q ≠ b} ≃
      {q : {q : Q // q ≠ a} // q ≠ ⟨b, hab.symm⟩} where
  toFun q := ⟨⟨q.1, q.2.1⟩, by
    intro h
    apply q.2.2
    exact congrArg Subtype.val h⟩
  invFun q := ⟨q.1.1, q.1.2, by
    intro h
    apply q.2
    apply Subtype.ext
    exact h⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Split a finite commutative product into its `a`, `b`, and remaining
coordinate factors. -/
theorem prod_split_two
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b) (f : Q → ℂ) :
    (∏ q, f q) = f a * f b * ∏ q : {q : Q // q ≠ a ∧ q ≠ b}, f q := by
  let b' : {q : Q // q ≠ a} := ⟨b, hab.symm⟩
  rw [Fintype.prod_eq_mul_prod_subtype_ne f a]
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun q : {q : Q // q ≠ a} => f q) b']
  change f a * (f b * ∏ q : {q : {q : Q // q ≠ a} // q ≠ b'}, f q.1) = _
  rw [mul_assoc]
  congr 2
  refine Fintype.prod_equiv (twoQubitRestEquiv a b hab).symm
    (fun q => f q) (fun q => f q.1) ?_
  intro q
  rfl

/-- The Pauli label on all coordinates except the two addressed ones. -/
def twoQubitRestPauliLabel
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3)) (a b : Q) :
    {q : Q // q ≠ a ∧ q ≠ b} → Option (Fin 3) :=
  fun q => P q.1

/-- Under the distinguished-coordinate split, a literal finite Pauli matrix
is the Kronecker product of its two addressed factors and its untouched
remainder. -/
theorem reindex_splitTwoQubitConfig_finitePauliMatrix
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b) (P : Q → Option (Fin 3)) :
    Matrix.reindex (splitTwoQubitConfig a b hab) (splitTwoQubitConfig a b hab)
        (finitePauliMatrix P) =
      Matrix.kronecker (boolTwoQubitPauli (P a) (P b))
        (finitePauliMatrix (twoQubitRestPauliLabel P a b)) := by
  ext x y
  rcases x with ⟨xlocal, xrest⟩
  rcases y with ⟨ylocal, yrest⟩
  change (∏ q, boolPauliOptionEntry (P q)
      ((splitTwoQubitConfig a b hab).symm (xlocal, xrest) q,
        (splitTwoQubitConfig a b hab).symm (ylocal, yrest) q)) = _
  rw [prod_split_two a b hab]
  simp [splitTwoQubitConfig, boolTwoQubitPauli, twoQubitRestPauliLabel,
    finitePauliMatrix, Matrix.kronecker, hab.symm]
  congr 2
  funext q
  simp [q.property.1, q.property.2]

/-- Reindexing commutes exactly with unitary conjugation. -/
theorem reindex_conjugation
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (U : Matrix.unitaryGroup α ℂ) (M : Matrix α α ℂ) :
    Matrix.reindex e e
        ((U : Matrix α α ℂ) * M * Matrix.conjTranspose (U : Matrix α α ℂ)) =
      ((unitaryGroupReindex e U : Matrix.unitaryGroup β ℂ) : Matrix β β ℂ) *
        Matrix.reindex e e M *
        Matrix.conjTranspose
          ((unitaryGroupReindex e U : Matrix.unitaryGroup β ℂ) : Matrix β β ℂ) := by
  change Matrix.reindexAlgEquiv ℂ ℂ e
      ((U : Matrix α α ℂ) * M * Matrix.conjTranspose (U : Matrix α α ℂ)) = _
  rw [map_mul, map_mul]
  rfl

/-- Conjugation by an arbitrary finite tensor gate factors into the two
component conjugations. -/
theorem finiteTensorGate_conjugation
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (U : Matrix.unitaryGroup α ℂ) (V : Matrix.unitaryGroup β ℂ)
    (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
    (Quantum.tensorGate U V : Matrix (α × β) (α × β) ℂ) *
        Matrix.kronecker M N *
        Matrix.conjTranspose
          (Quantum.tensorGate U V : Matrix (α × β) (α × β) ℂ) =
      Matrix.kronecker
        ((U : Matrix α α ℂ) * M * Matrix.conjTranspose (U : Matrix α α ℂ))
        ((V : Matrix β β ℂ) * N * Matrix.conjTranspose (V : Matrix β β ℂ)) := by
  simp only [Quantum.tensorGate_val]
  rw [Matrix.conjTranspose_kronecker]
  change ((U : Matrix α α ℂ) ⊗ₖ (V : Matrix β β ℂ)) *
      (M ⊗ₖ N) *
      (Matrix.conjTranspose (U : Matrix α α ℂ) ⊗ₖ
        Matrix.conjTranspose (V : Matrix β β ℂ)) = _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

/-- Replace Pauli labels on the two distinguished coordinates. -/
def updateTwoQubitPauliLabel
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3))
    (a b : Q) (pa pb : Option (Fin 3)) : Q → Option (Fin 3) :=
  Function.update (Function.update P a pa) b pb

/-- Updating the addressed labels leaves the remainder label unchanged. -/
theorem twoQubitRestPauliLabel_update
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3))
    (a b : Q) (pa pb : Option (Fin 3)) :
    twoQubitRestPauliLabel (updateTwoQubitPauliLabel P a b pa pb) a b =
      twoQubitRestPauliLabel P a b := by
  funext q
  simp [twoQubitRestPauliLabel, updateTwoQubitPauliLabel,
    q.property.1, q.property.2]

/-- Every exact local two-qubit transport lifts to the full finite Pauli
register, changing only the two selected labels. -/
theorem twoQubitLift_conjugation_of_local
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (P : Q → Option (Fin 3)) (pa pb : Option (Fin 3)) (c : ℂ)
    (hlocal : (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (P a) (P b) *
        Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      c • boolTwoQubitPauli pa pb) :
    (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) *
        finitePauliMatrix P *
        Matrix.conjTranspose (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) =
      c • finitePauliMatrix (updateTwoQubitPauliLabel P a b pa pb) := by
  apply (Matrix.reindexAlgEquiv ℂ ℂ (splitTwoQubitConfig a b hab)).injective
  change Matrix.reindex (splitTwoQubitConfig a b hab) (splitTwoQubitConfig a b hab) (_ * _ * _) = _
  rw [reindex_conjugation]
  rw [twoQubitLift, unitaryGroupReindex_apply_symm]
  rw [reindex_splitTwoQubitConfig_finitePauliMatrix]
  rw [finiteTensorGate_conjugation]
  simp
  change Matrix.kronecker
      ((U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (P a) (P b) *
        Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ))
      (finitePauliMatrix (twoQubitRestPauliLabel P a b)) = _
  rw [hlocal]
  change Matrix.kronecker (c • boolTwoQubitPauli pa pb)
      (finitePauliMatrix (twoQubitRestPauliLabel P a b)) =
    c • Matrix.reindex (splitTwoQubitConfig a b hab) (splitTwoQubitConfig a b hab)
      (finitePauliMatrix (updateTwoQubitPauliLabel P a b pa pb))
  rw [reindex_splitTwoQubitConfig_finitePauliMatrix]
  rw [twoQubitRestPauliLabel_update]
  ext x y
  rcases x with ⟨xlocal, xrest⟩
  rcases y with ⟨ylocal, yrest⟩
  simp [Matrix.kronecker]
  · simp [updateTwoQubitPauliLabel, hab, mul_assoc]

/-- Every finite Pauli string nontrivial on a selected pair has an explicit
lifted `SU(4)` gate that merges that local support onto the second selected
qubit. -/
theorem finitePauliMatrix_exists_twoQubitLift_transport
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (P : Q → Option (Fin 3)) (a b : Q) (hab : a ≠ b)
    (hlocal : P a ≠ none ∨ P b ≠ none) :
    ∃ U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ, ∃ c : ℂ, c ≠ 0 ∧
      (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) *
          finitePauliMatrix P *
          Matrix.conjTranspose (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) =
        c • finitePauliMatrix (updateTwoQubitPauliLabel P a b none (some 2)) := by
  let pq : boolNonidentityTwoQubitPauliLabel := ⟨(P a, P b), hlocal⟩
  obtain ⟨U, c, hc, htransport⟩ :=
    boolNonidentityTwoQubitPauli_exists_specialUnitaryTransport pq
  refine ⟨U, c, hc, ?_⟩
  exact twoQubitLift_conjugation_of_local a b hab U P none (some 2) c htransport

end

end GaloisForLFunctions.HTGeometry
