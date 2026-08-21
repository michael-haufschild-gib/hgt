/-
# Chen--Gupta--Li Proposition 5.1 axial finite reduction

Carries out CGL's finite residue summation on one of the three `S₁` axes.
The two zero coordinates are exactly orthogonalized; what remains is the
single additive twisted character sum times the analytic axial amplitude.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51FrequencyTail

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- One off-diagonal row contribution after the two zero-coordinate residue
correlations on the third-frequency axis have been evaluated. -/
def cglProposition51AxialRowTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (rst : Fin R × Fin R × Fin R) (m : ℤ) : ℂ :=
  (if (rows rst.1).character = (rows rst.2.1).character then (Q.value.totient : ℂ) else 0) *
    (if (rows rst.2.1).character = (rows rst.2.2).character then (Q.value.totient : ℂ) else 0) *
      cglProposition51AxialTwistedCharacterFactor Q
        (rows rst.2.2).character (rows rst.1).character m *
        cglProposition51AxialAnalyticAmplitude w N Q
          ((rows rst.1).time - (rows rst.2.1).time)
          ((rows rst.2.1).time - (rows rst.2.2).time)
          ((rows rst.2.2).time - (rows rst.1).time) m

/-- Exact CGL Proposition 5.1 finite reduction on one axial `S₁` frequency. -/
theorem cglProposition51_axialFrequencyTerm_eq_sum_rowTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) (m : ℤ) :
    cglLemma45OffDiagonalFrequencyTerm w N Q R rows
      (cglProposition51AxialFrequencyVector m) =
      ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
        (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)),
        cglProposition51AxialRowTerm w N Q R rows rst m := by
  unfold cglLemma45OffDiagonalFrequencyTerm
  dsimp only [cglLemma45OffDiagonalFrequencyIndex]
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro rst hrst
  exact cglProposition51_tripleResidue_axial_eq_orthogonalized w N Q
    (rows rst.1).character (rows rst.2.1).character
    (rows rst.2.1).character (rows rst.2.2).character
    (rows rst.2.2).character (rows rst.1).character
    ((rows rst.1).time - (rows rst.2.1).time)
    ((rows rst.2.1).time - (rows rst.2.2).time)
    ((rows rst.2.2).time - (rows rst.1).time) m

end RHTower
