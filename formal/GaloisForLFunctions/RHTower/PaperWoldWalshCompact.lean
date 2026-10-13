import GaloisForLFunctions.HTGeometry.DyadicWalshSeries
import GaloisForLFunctions.RHTower.PaperWoldHardyMaskedTransport
import GaloisForLFunctions.RHTower.PaperWoldCompositeDomain

/-! # Compact critical Wold operators obtained solely by sign cancellation

An explicit original-coordinate Walsh mask takes only `±1`. It turns both
critical complete operators into compact operators while preserving every
coefficient magnitude and their failure of Hilbert–Schmidt admission.
The proven compact-ideal trace therefore changes from infinity to zero.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The Walsh signs expressed in the original, uncompressed arithmetic coordinates. -/
def paperWoldWalshMask : PaperWoldMask := fun q =>
  ⟨dyadicWalshSign (q.1 / 2 - 1) (q.2 / 2 - 1), (dyadicWalshSign_norm _ _).le⟩

theorem paperWoldWalshMask_composite (n j : ℕ) :
    (paperWoldWalshMask (2 * n + 2, 2 * j + 2) : ℂ) = dyadicWalshSign n j := by
  simp [paperWoldWalshMask]

theorem paperWoldWalshMask_norm (q : ℕ × ℕ) : ‖(paperWoldWalshMask q : ℂ)‖ = 1 :=
  dyadicWalshSign_norm _ _

theorem paperWoldWalshMask_eq_one_or_neg_one (q : ℕ × ℕ) :
    (paperWoldWalshMask q : ℂ) = 1 ∨ (paperWoldWalshMask q : ℂ) = -1 :=
  dyadicWalshSign_eq_one_or_neg_one _ _

theorem paperWoldWalshHardy_eq :
    paperWoldHardyMaskedOperator paperWoldWalshMask = dyadicWalshOperator := by
  apply HasLpMatrix.ext (K := fun n j => dyadicWalshSign n j * paperWoldHardyEntry n j)
  · intro n j
    change paperWoldHardyMaskedOperator paperWoldWalshMask (lp.single 2 j 1) n = _
    rw [paperWoldHardyMaskedOperator_single, paperWoldWalshMask_composite]
  · intro n j
    change dyadicWalshOperator (lp.single 2 j 1) n = _
    rw [dyadicWalshOperator_single]
    congr 1
    by_cases h : n < j
    · simp only [paperWoldHardyEntry, if_pos h, one_div]
      congr 2
      ring
    · simp [paperWoldHardyEntry, h]

theorem paperWoldWalshHardy_compact :
    IsCompactOperator (paperWoldHardyMaskedOperator paperWoldWalshMask) := by
  rw [paperWoldWalshHardy_eq]
  exact dyadicWalshOperator_compact

theorem paperWoldWalshComposite_compact :
    IsCompactOperator (paperWoldCriticalCompositeMaskedOperator paperWoldWalshMask) :=
  (paperWoldHardyMaskedOperator_compact_iff paperWoldWalshMask).mp paperWoldWalshHardy_compact

theorem paperWoldWalshHardy_abs_entry (n j : ℕ) :
    ‖paperWoldHardyMaskedOperator paperWoldWalshMask (lp.single 2 j 1) n‖ =
      ‖paperWoldHardyEntry n j‖ := by
  rw [paperWoldHardyMaskedOperator_single, norm_mul, paperWoldWalshMask_norm, one_mul]

theorem paperWoldWalshComposite_abs_entry (n j : ℕ) :
    ‖paperWoldCriticalCompositeMaskedOperator paperWoldWalshMask (lp.single 2 j 1) n‖ =
      ‖paperWoldCompositeEntry (1 / 2) n j‖ := by
  rw [paperWoldCriticalCompositeMaskedOperator_single, norm_mul, paperWoldWalshMask_norm, one_mul]

theorem paperWoldWalshComposite_not_hilbertSchmidt :
    ¬ (paperWoldCriticalCompositeMaskedOperator paperWoldWalshMask).IsHilbertSchmidt := by
  intro h
  have hK := HilbertSchmidt.isHS_matrixOf h
  simp only [HilbertSchmidt.IsHS, HilbertSchmidt.matrixOf, paperWoldWalshComposite_abs_entry] at hK
  exact (lt_irrefl (1 / 2 : ℝ)) ((paperWoldCompositeEntry_isHS_iff (1 / 2)).mp hK)

theorem paperWoldWalshHardy_not_hilbertSchmidt :
    ¬ (paperWoldHardyMaskedOperator paperWoldWalshMask).IsHilbertSchmidt := by
  intro h
  apply paperWoldWalshComposite_not_hilbertSchmidt
  have hd := paperWoldHardyMaskedOperator_sub_composite_isHilbertSchmidt paperWoldWalshMask
  simpa only [sub_sub_cancel] using h.sub hd

theorem paperWoldWalshHardy_traceCost :
    compactOperatorTraceCost PaperWoldHistory (paperWoldHardyMaskedOperator paperWoldWalshMask) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr paperWoldWalshHardy_compact

theorem paperWoldWalshComposite_traceCost :
    compactOperatorTraceCost PaperWoldHistory
      (paperWoldCriticalCompositeMaskedOperator paperWoldWalshMask) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr paperWoldWalshComposite_compact

theorem paperWoldWalshHardy_compactIdealDistance :
    compactIdealDistance (paperWoldHardyMaskedOperator paperWoldWalshMask) = 0 :=
  compactIdealDistance_eq_zero_of_isCompactOperator _ paperWoldWalshHardy_compact

theorem paperWoldWalshComposite_compactIdealDistance :
    compactIdealDistance (paperWoldCriticalCompositeMaskedOperator paperWoldWalshMask) = 0 :=
  compactIdealDistance_eq_zero_of_isCompactOperator _ paperWoldWalshComposite_compact

end
end RHTower
