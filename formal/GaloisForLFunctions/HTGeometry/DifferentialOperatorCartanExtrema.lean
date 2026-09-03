import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpCartanInclusion
import GaloisForLFunctions.HTGeometry.DifferentialVariationalOperatorMatrixInterleaving

/-!
# Extreme completed Cartan coordinates of invertible differential-operator matrices

For every positive finite rank, sharp one-sided inclusions identify the bottom canonical Cartan
coordinate with minus the operator-matrix degree, and the top coordinate with the degree of the
inverse matrix.  These are exact endpoint identities for arbitrary units over `K[∂;δ]`.
-/

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {r : ℕ}

/-- A matrix unit has a nonzero entry attaining its matrix degree, including degree zero. -/
theorem exists_matrixUnit_entry_ne_zero_degree_eq_matDeg
    (U : (Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))ˣ) :
    ∃ i j, (U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) i j ≠ 0 ∧
      degree ((U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) i j) =
        matDeg (U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) := by
  let P := (U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))
  have hP0 : P ≠ 0 := Units.ne_zero U
  by_cases hn : matDeg P = 0
  · have hex : ∃ i j, P i j ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hP0
      funext i j
      exact hnone i j
    obtain ⟨i, j, hij⟩ := hex
    refine ⟨i, j, ?_, ?_⟩
    · change P i j ≠ 0
      exact hij
    · change degree (P i j) = matDeg P
      rw [hn]
      apply Nat.eq_zero_of_le_zero
      simpa [hn] using degree_le_matDeg P i j
  · have hex : ∃ i j, degree (P i j) = matDeg P := by
      by_contra hnone
      push Not at hnone
      have hle : ∀ i j, degree (P i j) ≤ matDeg P - 1 := by
        intro i j
        have hbound := degree_le_matDeg P i j
        have hlt : degree (P i j) < matDeg P :=
          lt_of_le_of_ne hbound (hnone i j)
        omega
      have hmat := matDeg_le hle
      omega
    obtain ⟨i, j, hij⟩ := hex
    refine ⟨i, j, ?_, ?_⟩
    · change P i j ≠ 0
      intro hzero
      rw [hzero, degree_zero] at hij
      omega
    · change degree (P i j) = matDeg P
      exact hij

/-- The bottom dominant Cartan coordinate is minus the degree of the operator matrix. -/
theorem completedPseudoDiffOpDominantRelativePosition_last_eq_neg_matDeg
    (U : (Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))ˣ) :
    completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1)))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv
            (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U))
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1))))
        (Fin.last r) =
      -(matDeg (U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) : ℤ) := by
  let A := completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1))
  let M := mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A) L
  let m := completedPseudoDiffOpDominantRelativePosition L M
  let n := matDeg (U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))
  change m (Fin.last r) = -(n : ℤ)
  have hmanti : Antitone m := completedPseudoDiffOpDominantRelativePosition_antitone L M
  have hupper :
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ)) M).carrier ≤
        L.carrier := by
    dsimp [M, L]
    apply (leftScale_mapMatrix_standard_carrier_le_iff
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ)) A).2
    intro i j
    rw [completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_val]
    change ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
      diffOpToCompletedPseudoRingHom
        ((U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) i j) ∈
      CompletedPseudoDiffOpInteger (K := K)
    rw [uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff]
    exact degree_le_matDeg _ i j
  have hlastLower : -(n : ℤ) ≤ m (Fin.last r) := by
    have h := (leftScale_uniformizer_mapMatrix_standard_carrier_le_iff_relativePosition
      A (n : ℤ)).1 (by simpa only [L, M] using hupper) (Fin.last r)
    change 0 ≤ m (Fin.last r) + (n : ℤ) at h
    omega
  have hsharp :
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ (-m (Fin.last r))) M).carrier ≤
        L.carrier := by
    dsimp [M, L]
    apply (leftScale_uniformizer_mapMatrix_standard_carrier_le_iff_relativePosition
      A (-m (Fin.last r))).2
    change ∀ i, 0 ≤ m i + -m (Fin.last r)
    intro i
    have hdom : m (Fin.last r) ≤ m i := hmanti (Fin.le_last i)
    omega
  obtain ⟨i, j, hij0, hijdeg⟩ := exists_matrixUnit_entry_ne_zero_degree_eq_matDeg U
  have hlastUpper : m (Fin.last r) ≤ -(n : ℤ) := by
    have hentry := (leftScale_mapMatrix_standard_carrier_le_iff
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ (-m (Fin.last r))) A).1
        (by simpa only [L, M] using hsharp) i j
    rw [completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_val] at hentry
    change ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (-m (Fin.last r)) :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
      diffOpToCompletedPseudoRingHom
        ((U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) i j) ∈
      CompletedPseudoDiffOpInteger (K := K) at hentry
    rw [uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int] at hentry
    rcases hentry with hzero | hdegree
    · exact absurd hzero hij0
    · rw [hijdeg] at hdegree
      omega
  omega

/-- The top dominant Cartan coordinate is the degree of the inverse operator matrix. -/
theorem completedPseudoDiffOpDominantRelativePosition_zero_eq_inv_matDeg
    (U : (Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))ˣ) :
    completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1)))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv
            (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U))
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1)))) 0 =
      (matDeg ((U⁻¹ : (Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))ˣ) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) : ℤ) := by
  let A := completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1))
  let M := mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A) L
  let m := completedPseudoDiffOpDominantRelativePosition L M
  let n := matDeg ((U⁻¹ : (Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))ˣ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))
  change m 0 = (n : ℤ)
  have hmanti : Antitone m := completedPseudoDiffOpDominantRelativePosition_antitone L M
  have hupper : L.carrier ≤
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(n : ℤ))) M).carrier := by
    dsimp [M, L]
    apply (standard_carrier_le_leftScale_mapMatrix_iff
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(n : ℤ))) A).2
    intro i j
    rw [show ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(n : ℤ)))⁻¹ :
        (CompletedPseudoDiffOp K)ˣ) =
      completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) by simp]
    rw [completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_inv_val]
    change ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
      diffOpToCompletedPseudoRingHom
        (((U⁻¹ : (Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))ˣ) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) i j) ∈
      CompletedPseudoDiffOpInteger (K := K)
    rw [uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff]
    exact degree_le_matDeg _ i j
  have hzeroUpper : m 0 ≤ (n : ℤ) := by
    have h := (standard_carrier_le_leftScale_uniformizer_mapMatrix_iff_relativePosition
      A (-(n : ℤ))).1 (by simpa only [L, M] using hupper) 0
    change m 0 + -(n : ℤ) ≤ 0 at h
    omega
  have hsharp : L.carrier ≤
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ (-m 0)) M).carrier := by
    dsimp [M, L]
    apply (standard_carrier_le_leftScale_uniformizer_mapMatrix_iff_relativePosition
      A (-m 0)).2
    change ∀ i, m i + -m 0 ≤ 0
    intro i
    have hdom : m i ≤ m 0 := hmanti (Fin.zero_le i)
    omega
  obtain ⟨i, j, hij0, hijdeg⟩ :=
    exists_matrixUnit_entry_ne_zero_degree_eq_matDeg (U⁻¹)
  have hzeroLower : (n : ℤ) ≤ m 0 := by
    have hentry := (standard_carrier_le_leftScale_mapMatrix_iff
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ (-m 0)) A).1
        (by simpa only [L, M] using hsharp) i j
    rw [show ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (-m 0))⁻¹ :
        (CompletedPseudoDiffOp K)ˣ) =
      completedPseudoDiffOpUniformizerUnit (K := K) ^ m 0 by simp] at hentry
    rw [completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_inv_val] at hentry
    change ((completedPseudoDiffOpUniformizerUnit (K := K) ^ m 0 :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
      diffOpToCompletedPseudoRingHom
        (((U⁻¹ : (Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))ˣ) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) i j) ∈
      CompletedPseudoDiffOpInteger (K := K) at hentry
    rw [uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int] at hentry
    rcases hentry with hzero | hdegree
    · exact absurd hzero hij0
    · rw [hijdeg] at hdegree
      omega
  omega

/-- Reversing the ordered lattice pair makes the top dominant Cartan coordinate equal to the
degree of the original operator matrix. -/
theorem completedPseudoDiffOpDominantRelativePosition_mapMatrix_standard_zero_eq_matDeg
    (U : (Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K))ˣ) :
    completedPseudoDiffOpDominantRelativePosition
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv
            (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U))
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1))))
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1))) 0 =
      (matDeg (U : Matrix (Fin (r + 1)) (Fin (r + 1)) (DiffOp K)) : ℤ) := by
  let A := completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U
  let B := completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U⁻¹
  let eA := completedPseudoDiffOpMatrixLinearEquiv A
  let eB := completedPseudoDiffOpMatrixLinearEquiv B
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin (r + 1))
  let M := mapCompletedPseudoDiffOpLatticeLinear eA L
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_mul]
    change Units.map
      (diffOpToCompletedPseudoRingHom (K := K)).mapMatrix.toMonoidHom (U * U⁻¹) = 1
    have hU : U * U⁻¹ = 1 := by simp
    rw [hU]
    exact map_one _
  have hmapM : mapCompletedPseudoDiffOpLatticeLinear eB M = L := by
    dsimp [M]
    rw [mapCompletedPseudoDiffOpLatticeLinear_trans]
    change mapCompletedPseudoDiffOpLatticeLinear
      ((completedPseudoDiffOpMatrixLinearEquiv A).trans
        (completedPseudoDiffOpMatrixLinearEquiv B)) L = L
    rw [completedPseudoDiffOpMatrixLinearEquiv_mul, hAB,
      completedPseudoDiffOpMatrixLinearEquiv_one,
      mapCompletedPseudoDiffOpLatticeLinear_refl]
  have hinv := completedPseudoDiffOpDominantRelativePosition_zero_eq_inv_matDeg
    (K := K) (r := r) U⁻¹
  have htransport := completedPseudoDiffOpDominantRelativePosition_mapLinear eB M L
  change completedPseudoDiffOpDominantRelativePosition M L 0 = _
  rw [← htransport]
  rw [hmapM]
  simpa [B, eB, L] using hinv

end

end GaloisForLFunctions.HTGeometry.DiffOp
