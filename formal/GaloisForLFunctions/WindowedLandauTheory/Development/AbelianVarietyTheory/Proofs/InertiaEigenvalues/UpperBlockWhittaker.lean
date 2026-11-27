import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularLeadingColumns

/-! On a unitriangular matrix with identity leading block, the Whittaker
character splits into one boundary entry and the character of the trailing block. -/

noncomputable section
open scoped Classical

open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

private theorem entN_fin {n : ℕ} (M : Mt g n) (i j : Fin n) : entN M i.val j.val = M i j := by
  simp [entN, i.isLt, j.isLt]

/-- Only the last row of the first rectangle column contributes across the block boundary. -/
theorem superdiagonal_upperBlock (X : Matrix (Fin (a + 1)) (Fin (b + 1)) (ZMod g))
    (D : Mt g (b + 1)) :
    (∑ i ∈ Finset.range (a + 1 + (b + 1) - 1),
      entN (upperBlockMatrix (1 : Mt g (a + 1)) X D) i (i + 1)) =
      X (Fin.last a) 0 + ∑ i ∈ Finset.range b, entN D i (i + 1) := by
  let M := upperBlockMatrix (1 : Mt g (a + 1)) X D
  change (∑ i ∈ Finset.range (a + 1 + (b + 1) - 1), entN M i (i + 1)) = _
  rw [show a + 1 + (b + 1) - 1 = (a + 1) + b by omega, Finset.sum_range_add]
  congr 1
  · rw [Finset.sum_range_succ]
    have hz : (∑ i ∈ Finset.range a, entN M i (i + 1)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have h := Finset.mem_range.mp hi
      let i' : Fin (a + 1) := ⟨i, by omega⟩
      let j' : Fin (a + 1) := ⟨i + 1, by omega⟩
      have hne : i' ≠ j' := fun e => Nat.ne_of_lt (Nat.lt_succ_self i) (congrArg Fin.val e)
      change entN M (Fin.castAdd (b + 1) i').val (Fin.castAdd (b + 1) j').val = 0
      rw [entN_fin]
      simp [M, upperBlockMatrix, hne]
    rw [hz, zero_add]
    change entN M (Fin.castAdd (b + 1) (Fin.last a)).val (Fin.natAdd (a + 1) (0 : Fin (b + 1))).val = _
    rw [entN_fin]
    simp [M, upperBlockMatrix]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have h := Finset.mem_range.mp hi
    let i' : Fin (b + 1) := ⟨i, by omega⟩
    let j' : Fin (b + 1) := ⟨i + 1, by omega⟩
    have he : (a + 1 + i) + 1 = (Fin.natAdd (a + 1) j').val := by
      change (a + 1 + i) + 1 = (a + 1) + (i + 1)
      omega
    rw [he]
    change entN M (Fin.natAdd (a + 1) i').val (Fin.natAdd (a + 1) j').val = entN D i'.val j'.val
    rw [entN_fin, entN_fin]
    simp [M, upperBlockMatrix]

/-- The Whittaker character on a block matrix factors into a column weight and the tail weight. -/
theorem whittakerCharacter_upperBlock (ψ : AddChar (ZMod g) ℂ)
    (X : Matrix (Fin (a + 1)) (Fin (b + 1)) (ZMod g))
    (D : upperUnitriangular g (b + 1)) :
    (whittakerCharacter ψ (a + 1 + (b + 1))
      ⟨upperBlockUnit 1 X D.val, isUniUp_upperBlockMatrix X D.property⟩ : ℂ) =
      ψ (X (Fin.last a) 0) * (whittakerCharacter ψ (b + 1) D : ℂ) := by
  change ψ (∑ i ∈ Finset.range (a + 1 + (b + 1) - 1),
    entN (upperBlockMatrix (1 : Mt g (a + 1)) X D.val.val) i (i + 1)) = _
  exact (congrArg ψ (superdiagonal_upperBlock X D.val.val)).trans (AddChar.map_add_eq_mul ψ _ _)

end GlobalTheory.GLq
