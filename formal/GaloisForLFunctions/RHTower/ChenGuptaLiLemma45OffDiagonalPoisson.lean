/-
# Chen--Gupta--Li Lemma 4.5 off-diagonal Poisson assembly

Applies the established three-coordinate Poisson identity only to the
non-all-equal row triples.  Its global frequency term is exactly CGL's
`I_m` before the separate treatment of the zero vector.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45DiagonalPoisson

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The finite row/residue carrier of CGL Lemma 4.5's non-all-equal term. -/
def cglLemma45OffDiagonalFrequencyIndex (Q : CGLPositiveModulus) (R : ℕ) :
    Finset ((((Fin R × Fin R × Fin R) × ZMod Q.value) × ZMod Q.value) × ZMod Q.value) :=
  ((((cglCharacterDyadicGramCubicIndexSet R).filter
    (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)) ×ˢ Finset.univ) ×ˢ
      Finset.univ) ×ˢ Finset.univ)

/-- CGL's source coefficient `I_m`, with the non-all-equal row condition
implemented by its literal finite index carrier. -/
def cglLemma45OffDiagonalFrequencyTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) (m : (ℤ × ℤ) × ℤ) : ℂ :=
  ∑ i ∈ cglLemma45OffDiagonalFrequencyIndex Q R,
    cglLemma45TripleFrequencyTerm w N Q
      (rows i.1.1.1.1).character (rows i.1.1.1.2.1).character
      (rows i.1.1.1.2.1).character (rows i.1.1.1.2.2).character
      (rows i.1.1.1.2.2).character (rows i.1.1.1.1).character
      ((rows i.1.1.1.1).time - (rows i.1.1.1.2.1).time)
      ((rows i.1.1.1.2.1).time - (rows i.1.1.1.2.2).time)
      ((rows i.1.1.1.2.2).time - (rows i.1.1.1.1).time)
      i.1.1.2 i.1.2 i.2 m

/-- **CGL Lemma 4.5, source `I_m` reindexing.** The literal non-all-equal
cubic trace is exactly the global `Z³` series of the source frequency terms.
The finite/infinite interchange is certified by the constructed absolute
Schwartz summability of each fixed row/residue index. -/
theorem cglLemma45_offDiagonal_eq_tsum_frequencyTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglCharacterDyadicWeightedGramCubicOffDiagonal N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
      ∑' m : (ℤ × ℤ) × ℤ, cglLemma45OffDiagonalFrequencyTerm w N Q R rows m := by
  let s := cglLemma45OffDiagonalFrequencyIndex Q R
  let f : ((((Fin R × Fin R × Fin R) × ZMod Q.value) × ZMod Q.value) ×
      ZMod Q.value) → (ℤ × ℤ) × ℤ → ℂ := fun i m =>
    cglLemma45TripleFrequencyTerm w N Q
      (rows i.1.1.1.1).character (rows i.1.1.1.2.1).character
      (rows i.1.1.1.2.1).character (rows i.1.1.1.2.2).character
      (rows i.1.1.1.2.2).character (rows i.1.1.1.1).character
      ((rows i.1.1.1.1).time - (rows i.1.1.1.2.1).time)
      ((rows i.1.1.1.2.1).time - (rows i.1.1.1.2.2).time)
      ((rows i.1.1.1.2.2).time - (rows i.1.1.1.1).time)
      i.1.1.2 i.1.2 i.2 m
  have hsingle : ∀ i ∈ s, Summable (f i) := by
    intro i hi
    simpa only [f] using
      (cglLemma45TripleFrequencyTerm_summable_norm w N Q
        (rows i.1.1.1.1).character (rows i.1.1.1.2.1).character
        (rows i.1.1.1.2.1).character (rows i.1.1.1.2.2).character
        (rows i.1.1.1.2.2).character (rows i.1.1.1.1).character
        ((rows i.1.1.1.1).time - (rows i.1.1.1.2.1).time)
        ((rows i.1.1.1.2.1).time - (rows i.1.1.1.2.2).time)
        ((rows i.1.1.1.2.2).time - (rows i.1.1.1.1).time)
        i.1.1.2 i.1.2 i.2).of_norm
  have hswap := Summable.tsum_finsetSum hsingle
  calc
    cglCharacterDyadicWeightedGramCubicOffDiagonal N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
        ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
          (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)),
          ∑ a₁ : ZMod Q.value, ∑ a₂ : ZMod Q.value, ∑ a₃ : ZMod Q.value,
            ∑' m : (ℤ × ℤ) × ℤ,
              cglLemma45TripleFrequencyTerm w N Q
                (rows rst.1).character (rows rst.2.1).character
                (rows rst.2.1).character (rows rst.2.2).character
                (rows rst.2.2).character (rows rst.1).character
                ((rows rst.1).time - (rows rst.2.1).time)
                ((rows rst.2.1).time - (rows rst.2.2).time)
                ((rows rst.2.2).time - (rows rst.1).time)
                a₁ a₂ a₃ m := by
      unfold cglCharacterDyadicWeightedGramCubicOffDiagonal
      apply Finset.sum_congr rfl
      intro rst hrst
      exact cglLemma45_cubicRow_eq_threeFrequencySum w N Q R rows rst
    _ = ∑ i ∈ s, ∑' m : (ℤ × ℤ) × ℤ, f i m := by
      dsimp only [s, f, cglLemma45OffDiagonalFrequencyIndex]
      rw [Finset.sum_product, Finset.sum_product, Finset.sum_product]
    _ = ∑' m : (ℤ × ℤ) × ℤ, ∑ i ∈ s, f i m := hswap.symm
    _ = ∑' m : (ℤ × ℤ) × ℤ, cglLemma45OffDiagonalFrequencyTerm w N Q R rows m := by
      rfl

end RHTower
