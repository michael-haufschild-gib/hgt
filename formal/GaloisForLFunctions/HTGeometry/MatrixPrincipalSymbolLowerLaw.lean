import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolHypertranscendenceHorizon

/-!
# Explicit lower-layer matrix principal laws

This file removes the finite packet-realization interface as an unexplained external object.  A
matrix principal law consists of the prescribed diagonal symbol blocks plus coefficients pointing
strictly into earlier filtration layers.  Such a law automatically realizes the block principal
symbol packet and therefore satisfies the exact complete hypertranscendence criterion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

/-- The canonical diagonal matrix assembled from a finite sequence of matrix principal symbols. -/
def matrixPrincipalBlockDiagonal {N : ℕ}
    (symbol : Fin N → Matrix ι ι K) :
    Matrix (Fin N × ι) (Fin N × ι) K :=
  fun p q ↦ if p.1 = q.1 then symbol p.1 p.2 q.2 else 0

/-- An explicit finite-stage lower principal law.  The remainder matrix has no coefficient on the
same or any later layer; adding the canonical diagonal symbols produces the observable packet. -/
def MatrixPrincipalLowerLaw
    (u y : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K) : Prop :=
  ∀ N : ℕ, ∃ R : Matrix (Fin N × ι) (Fin N × ι) K,
    (∀ p q, (p.1 : ℕ) ≤ (q.1 : ℕ) → R p q = 0) ∧
      (fun p : Fin N × ι ↦ y p.1 p.2) =
        matrixLinearForms
          (R + matrixPrincipalBlockDiagonal (fun n : Fin N ↦ symbol n))
          (fun p : Fin N × ι ↦ u p.1 p.2)

omit [Fintype ι] [DecidableEq ι] in
/-- The canonical symbol matrix is block diagonal for the reverse filtration order. -/
theorem matrixPrincipalBlockDiagonal_blockTriangular
    {N : ℕ} (symbol : Fin N → Matrix ι ι K) :
    (matrixPrincipalBlockDiagonal symbol).BlockTriangular matrixPrincipalLayerOrder := by
  intro p q hpq
  have hlt : (p.1 : ℕ) < (q.1 : ℕ) := hpq
  have hne : p.1 ≠ q.1 := ne_of_lt hlt
  simp [matrixPrincipalBlockDiagonal, hne]

omit [Fintype ι] [DecidableEq ι] in
/-- Every diagonal fiber of the canonical block matrix is exactly the corresponding symbol after
the canonical reindexing of that layer. -/
theorem matrixPrincipalBlockDiagonal_toSquareBlock
    {N : ℕ} (symbol : Fin N → Matrix ι ι K) (n : Fin N) :
    (matrixPrincipalBlockDiagonal symbol).toSquareBlock
        matrixPrincipalLayerOrder (OrderDual.toDual n) =
      Matrix.reindex (matrixPrincipalLayerEquiv n) (matrixPrincipalLayerEquiv n) (symbol n) := by
  ext p q
  have hp : p.1.1 = n := congrArg OrderDual.ofDual p.2
  have hq : q.1.1 = n := congrArg OrderDual.ofDual q.2
  change (if p.1.1 = q.1.1 then symbol p.1.1 p.1.2 q.1.2 else 0) =
    symbol n p.1.2 q.1.2
  simp [hp, hq]

omit [DecidableEq ι] in
/-- Explicit strict-lower-layer laws produce the intrinsic finite packet realization. -/
theorem matrixPrincipalPacketRealization_of_lowerLaw
    (u y : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K)
    (hlaw : MatrixPrincipalLowerLaw u y symbol) :
    MatrixPrincipalPacketRealization u y symbol := by
  intro N
  obtain ⟨R, hR, hpacket⟩ := hlaw N
  let B : Matrix (Fin N × ι) (Fin N × ι) K :=
    matrixPrincipalBlockDiagonal (fun n : Fin N ↦ symbol n)
  refine ⟨R + B, hpacket, ?_, ?_⟩
  · intro p q hpq
    have hlt : (p.1 : ℕ) < (q.1 : ℕ) := hpq
    rw [Matrix.add_apply, hR p q (Nat.le_of_lt hlt)]
    have hne : p.1 ≠ q.1 := ne_of_lt hlt
    simp [B, matrixPrincipalBlockDiagonal, hne]
  · intro n
    change R.toSquareBlock matrixPrincipalLayerOrder (OrderDual.toDual n) +
      B.toSquareBlock matrixPrincipalLayerOrder (OrderDual.toDual n) = _
    have hRblock :
        R.toSquareBlock matrixPrincipalLayerOrder (OrderDual.toDual n) = 0 := by
      ext p q
      have hp : p.1.1 = n := congrArg OrderDual.ofDual p.2
      have hq : q.1.1 = n := congrArg OrderDual.ofDual q.2
      exact hR p.1 q.1 (by simp [hp, hq])
    rw [hRblock, zero_add]
    exact matrixPrincipalBlockDiagonal_toSquareBlock
      (fun n : Fin N ↦ symbol n) n

/-- The complete packet criterion stated directly from explicit strict-lower-layer laws. -/
theorem matrixPrincipalLowerLaw_algebraicIndependent_iff
    (u y : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K)
    (hlaw : MatrixPrincipalLowerLaw u y symbol)
    (hu : AlgebraicIndependent K (fun p : ℕ × ι ↦ u p.1 p.2)) :
    AlgebraicIndependent K (fun p : ℕ × ι ↦ y p.1 p.2) ↔
      ∀ n : ℕ, (symbol n).det ≠ 0 :=
  matrixPrincipalPacket_algebraicIndependent_iff u y symbol
    (matrixPrincipalPacketRealization_of_lowerLaw u y symbol hlaw) hu

end

end GaloisForLFunctions.HTGeometry
