import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialSourcePower

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- Cyclically rotate the three frequency coordinates used in CGL Proposition 5.1. -/
def cglProposition51RotateFrequency : (ℤ × ℤ) × ℤ → (ℤ × ℤ) × ℤ :=
  fun m => ((m.1.2, m.2), m.1.1)

/-- Cyclically rotate the three row indices used in a CGL cubic coefficient. -/
def cglProposition51RotateRowTriple {R : ℕ} :
    (Fin R × Fin R × Fin R) ≃ (Fin R × Fin R × Fin R) where
  toFun rst := (rst.2.1, rst.2.2, rst.1)
  invFun rst := (rst.2.2, rst.1, rst.2.1)
  left_inv rst := by cases rst; rfl
  right_inv rst := by cases rst; rfl

/-- Simultaneous cyclic rotation of rows and residue coordinates in a CGL cubic coefficient. -/
def cglProposition51RotateFrequencyIndex (Q : CGLPositiveModulus) (R : ℕ) :
    ((((Fin R × Fin R × Fin R) × ZMod Q.value) × ZMod Q.value) × ZMod Q.value) ≃
      ((((Fin R × Fin R × Fin R) × ZMod Q.value) × ZMod Q.value) × ZMod Q.value) where
  toFun i := (((cglProposition51RotateRowTriple i.1.1.1, i.1.2), i.2), i.1.1.2)
  invFun i := (((cglProposition51RotateRowTriple.symm i.1.1.1, i.2), i.1.1.2), i.1.2)
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

theorem cglProposition51_rotateRowTriple_offDiagonal_iff
    {R : ℕ} (rst : Fin R × Fin R × Fin R) :
    ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2) ↔
      ¬ ((cglProposition51RotateRowTriple rst).1 =
        (cglProposition51RotateRowTriple rst).2.1 ∧
        (cglProposition51RotateRowTriple rst).2.1 =
          (cglProposition51RotateRowTriple rst).2.2) := by
  constructor
  · intro h hrot
    apply h
    exact ⟨hrot.2.symm.trans hrot.1.symm, hrot.1⟩
  · intro h hold
    apply h
    exact ⟨hold.2, hold.2.symm.trans hold.1.symm⟩

theorem cglProposition51_rotateFrequencyIndex_mem_iff
    (Q : CGLPositiveModulus) (R : ℕ)
    (i : (((Fin R × Fin R × Fin R) × ZMod Q.value) × ZMod Q.value) × ZMod Q.value) :
    i ∈ cglLemma45OffDiagonalFrequencyIndex Q R ↔
      cglProposition51RotateFrequencyIndex Q R i ∈ cglLemma45OffDiagonalFrequencyIndex Q R := by
  simpa [cglLemma45OffDiagonalFrequencyIndex, cglCharacterDyadicGramCubicIndexSet,
    cglProposition51RotateFrequencyIndex, cglProposition51RotateRowTriple] using
    cglProposition51_rotateRowTriple_offDiagonal_iff i.1.1.1

/-- The full CGL off-diagonal coefficient is invariant under simultaneous cyclic rotation. -/
theorem cglProposition51_offDiagonalFrequencyTerm_rotate
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (m : (ℤ × ℤ) × ℤ) :
    cglLemma45OffDiagonalFrequencyTerm w N Q R rows m =
      cglLemma45OffDiagonalFrequencyTerm w N Q R rows
        (cglProposition51RotateFrequency m) := by
  unfold cglLemma45OffDiagonalFrequencyTerm
  refine Finset.sum_equiv (cglProposition51RotateFrequencyIndex Q R) ?_ ?_
  · intro i
    exact cglProposition51_rotateFrequencyIndex_mem_iff Q R i
  · intro i hi
    dsimp [cglProposition51RotateFrequencyIndex, cglProposition51RotateRowTriple,
      cglProposition51RotateFrequency]
    unfold cglLemma45TripleFrequencyTerm
    ring

end RHTower
