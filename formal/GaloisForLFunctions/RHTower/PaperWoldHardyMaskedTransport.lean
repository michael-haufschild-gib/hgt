import GaloisForLFunctions.RHTower.PaperWoldHardyQuotient

/-! # Hardy transport for every bounded mask on the original arithmetic coordinates

Both masked operators are constructed on the complete history space. Their
exact difference has one common Hilbert–Schmidt budget, so every window or
phase selection has the same compact-ideal invariants in the two matrices.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- Pull an original-coordinate selection onto the actual even-composite indices. -/
def paperWoldOriginalCompositeMask (m : PaperWoldMask) : PaperWoldMask :=
  fun q => m (2 * q.1 + 2, 2 * q.2 + 2)

def PaperHardy.Kernel.mask (K : PaperHardy.Kernel) (m : PaperWoldMask) : PaperHardy.Kernel where
  entry n j := (m (n, j) : ℂ) * K.entry n j
  bound n j := by
    rw [norm_mul]
    exact ((mul_le_mul_of_nonneg_right (m (n, j)).property (norm_nonneg _)).trans_eq
      (one_mul _)).trans (K.bound n j)

def paperWoldHardyMaskedOperator (m : PaperWoldMask) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  (paperWoldHardyKernel.mask (paperWoldOriginalCompositeMask m)).toOperator

def paperWoldCriticalCompositeMaskedOperator (m : PaperWoldMask) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  (paperWoldCriticalCompositeKernel.mask (paperWoldOriginalCompositeMask m)).toOperator

theorem paperWoldHardyMaskedOperator_single (m : PaperWoldMask) (n j : ℕ) :
    paperWoldHardyMaskedOperator m (lp.single 2 j (1 : ℂ)) n =
      (m (2 * n + 2, 2 * j + 2) : ℂ) * paperWoldHardyEntry n j :=
  (paperWoldHardyKernel.mask (paperWoldOriginalCompositeMask m)).toOperator_single n j

theorem paperWoldCriticalCompositeMaskedOperator_single (m : PaperWoldMask) (n j : ℕ) :
    paperWoldCriticalCompositeMaskedOperator m (lp.single 2 j (1 : ℂ)) n =
      (m (2 * n + 2, 2 * j + 2) : ℂ) * paperWoldCompositeEntry (1 / 2) n j :=
  (paperWoldCriticalCompositeKernel.mask (paperWoldOriginalCompositeMask m)).toOperator_single n j

theorem paperWoldHardyMaskedOperator_norm_le (m : PaperWoldMask) :
    ‖paperWoldHardyMaskedOperator m‖ ≤ 5 :=
  (paperWoldHardyKernel.mask (paperWoldOriginalCompositeMask m)).norm_toOperator_le

theorem paperWoldCriticalCompositeMaskedOperator_norm_le (m : PaperWoldMask) :
    ‖paperWoldCriticalCompositeMaskedOperator m‖ ≤ 5 :=
  (paperWoldCriticalCompositeKernel.mask (paperWoldOriginalCompositeMask m)).norm_toOperator_le

theorem paperWoldHardyMaskedOperator_full :
    paperWoldHardyMaskedOperator paperWoldFullMask = paperWoldHardyOperator := by
  apply HasLpMatrix.ext (K := paperWoldHardyEntry)
  · intro n j
    simpa only [lpBasisVec, paperWoldFullMask, one_mul] using
      paperWoldHardyMaskedOperator_single paperWoldFullMask n j
  · exact paperWoldHardyOperator_single

theorem paperWoldCriticalCompositeMaskedOperator_full :
    paperWoldCriticalCompositeMaskedOperator paperWoldFullMask = paperWoldCriticalCompositeOperator := by
  apply HasLpMatrix.ext (K := paperWoldCompositeEntry (1 / 2))
  · intro n j
    simpa only [lpBasisVec, paperWoldFullMask, one_mul] using
      paperWoldCriticalCompositeMaskedOperator_single paperWoldFullMask n j
  · exact paperWoldCriticalCompositeOperator_single

def paperWoldHardyMaskedDefect (m : PaperWoldMask) (q : ℕ × ℕ) : ℂ :=
  (paperWoldOriginalCompositeMask m q : ℂ) * paperWoldHardyDefect q

theorem paperWoldHardyMaskedDefect_norm_le (m : PaperWoldMask) (q : ℕ × ℕ) :
    ‖paperWoldHardyMaskedDefect m q‖ ≤ ‖paperWoldHardyDefect q‖ := by
  rw [paperWoldHardyMaskedDefect, norm_mul]
  exact (mul_le_mul_of_nonneg_right (paperWoldOriginalCompositeMask m q).property
    (norm_nonneg _)).trans_eq (one_mul _)

theorem paperWoldHardyMaskedDefect_isHS (m : PaperWoldMask) :
    HilbertSchmidt.IsHS (paperWoldHardyMaskedDefect m) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => pow_le_pow_left₀ (norm_nonneg _) (paperWoldHardyMaskedDefect_norm_le m q) 2)
    paperWoldHardyDefect_isHS

theorem paperWoldHardyMaskedDefect_hsNormSq_le (m : PaperWoldMask) :
    HilbertSchmidt.hsNormSq (paperWoldHardyMaskedDefect m) ≤ HilbertSchmidt.hsNormSq paperWoldHardyDefect :=
  Summable.tsum_le_tsum
    (fun q => pow_le_pow_left₀ (norm_nonneg _) (paperWoldHardyMaskedDefect_norm_le m q) 2)
    (paperWoldHardyMaskedDefect_isHS m) paperWoldHardyDefect_isHS

theorem paperWoldHardyMaskedOperator_sub_composite (m : PaperWoldMask) :
    paperWoldHardyMaskedOperator m - paperWoldCriticalCompositeMaskedOperator m =
      HilbertSchmidt.toOperator (paperWoldHardyMaskedDefect_isHS m) := by
  apply HasLpMatrix.ext (K := fun n j => paperWoldHardyMaskedDefect m (n, j))
  · intro n j
    change (paperWoldHardyMaskedOperator m - paperWoldCriticalCompositeMaskedOperator m)
      (lp.single 2 j (1 : ℂ)) n = _
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply,
      paperWoldHardyMaskedOperator_single, paperWoldCriticalCompositeMaskedOperator_single,
      paperWoldHardyMaskedDefect, paperWoldOriginalCompositeMask, paperWoldHardyDefect, mul_sub]
  · intro n j
    exact HilbertSchmidt.toOperator_single (paperWoldHardyMaskedDefect_isHS m) n j

theorem paperWoldHardyMaskedOperator_sub_composite_isHilbertSchmidt (m : PaperWoldMask) :
    (paperWoldHardyMaskedOperator m - paperWoldCriticalCompositeMaskedOperator m).IsHilbertSchmidt := by
  rw [paperWoldHardyMaskedOperator_sub_composite]
  exact HilbertSchmidt.isHilbertSchmidt_toOperator _

theorem paperWoldHardyMaskedOperator_sub_composite_compact (m : PaperWoldMask) :
    IsCompactOperator (paperWoldHardyMaskedOperator m - paperWoldCriticalCompositeMaskedOperator m) :=
  (paperWoldHardyMaskedOperator_sub_composite_isHilbertSchmidt m).isCompactOperator

theorem paperWoldHardyMaskedOperator_add_traceCost (m : PaperWoldMask)
    (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) :
    compactOperatorTraceCost PaperWoldHistory (T + paperWoldHardyMaskedOperator m) =
      compactOperatorTraceCost PaperWoldHistory (T + paperWoldCriticalCompositeMaskedOperator m) := by
  have h := compactOperatorTraceCost_add_compact (T + paperWoldCriticalCompositeMaskedOperator m)
    ⟨paperWoldHardyMaskedOperator m - paperWoldCriticalCompositeMaskedOperator m,
      paperWoldHardyMaskedOperator_sub_composite_compact m⟩
  convert h using 1
  congr 1
  module

theorem paperWoldHardyMaskedOperator_add_distance (m : PaperWoldMask)
    (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) :
    compactIdealDistance (T + paperWoldHardyMaskedOperator m) =
      compactIdealDistance (T + paperWoldCriticalCompositeMaskedOperator m) := by
  have h := paperCompactIdealDistance_add_compact (T + paperWoldCriticalCompositeMaskedOperator m)
    ⟨paperWoldHardyMaskedOperator m - paperWoldCriticalCompositeMaskedOperator m,
      paperWoldHardyMaskedOperator_sub_composite_compact m⟩
  convert h using 1
  congr 1
  module

theorem paperWoldHardyMaskedOperator_compact_iff (m : PaperWoldMask) :
    IsCompactOperator (paperWoldHardyMaskedOperator m) ↔
      IsCompactOperator (paperWoldCriticalCompositeMaskedOperator m) := by
  have h := paperWoldHardyMaskedOperator_add_traceCost m 0
  simp only [zero_add] at h
  rw [← compactOperatorTraceCost_eq_zero_iff, ← compactOperatorTraceCost_eq_zero_iff, h]

end
end RHTower
