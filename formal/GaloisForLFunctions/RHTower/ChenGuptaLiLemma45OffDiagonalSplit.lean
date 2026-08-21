/-
# Chen--Gupta--Li Lemma 4.5 off-diagonal frequency split

Builds summability of the source non-all-equal frequency term and isolates its
origin.  Together with the diagonal factor this is CGL's exact
`Z + Z' + sum_(m != 0) I_m` expansion before estimating `Z'`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45OffDiagonalPoisson

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- CGL's `I_m` restricted to the literal carrier `Z³ \ {0}`. -/
def cglLemma45OffDiagonalNonzeroFrequencyTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))}) : ℂ :=
  cglLemma45OffDiagonalFrequencyTerm w N Q R rows m

/-- CGL's off-diagonal source coefficient is summable, derived by finite
induction from fixed row/residue Schwartz certificates. -/
theorem cglLemma45OffDiagonalFrequencyTerm_summable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    Summable (cglLemma45OffDiagonalFrequencyTerm w N Q R rows) := by
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
  have hsingle : ∀ i ∈ cglLemma45OffDiagonalFrequencyIndex Q R, Summable (f i) := by
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
  have finiteSum_summable : ∀ u :
      Finset ((((Fin R × Fin R × Fin R) × ZMod Q.value) × ZMod Q.value) × ZMod Q.value),
      (∀ i ∈ u, Summable (f i)) → Summable (fun m => ∑ i ∈ u, f i m) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      intro hu
      simp
    | insert a u ha ih =>
      intro hu
      simpa [Finset.sum_insert, ha] using
        (hu a (by simp)).add (ih (fun i hi => hu i (by simp [hi])))
  change Summable (fun m => ∑ i ∈ cglLemma45OffDiagonalFrequencyIndex Q R, f i m)
  exact finiteSum_summable (cglLemma45OffDiagonalFrequencyIndex Q R) hsingle

/-- **CGL Lemma 4.5, exact source expansion.** This is the source identity
`tr((MM*)³) = Z + Z' + sum_(m != 0) I_m`, before the reciprocal-decay estimate
for `Z'`. -/
theorem cglLemma45_cubicTrace_eq_diagonal_add_zeroOffDiagonal_add_nonzero
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglCharacterDyadicWeightedGramCubicTrace N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
      (R : ℂ) * cglLemma45DiagonalPoissonMass w N Q ^ 3 +
        cglLemma45OffDiagonalFrequencyTerm w N Q R rows 0 +
        ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45OffDiagonalNonzeroFrequencyTerm w N Q R rows m := by
  rw [cglLemma45_cubicTrace_eq_diagonalPoisson_add_offDiagonal,
    cglLemma45_offDiagonal_eq_tsum_frequencyTerm]
  have hsum := cglLemma45OffDiagonalFrequencyTerm_summable w N Q R rows
  have hsplit := hsum.sum_add_tsum_subtype_compl ({0} : Finset ((ℤ × ℤ) × ℤ))
  rw [hsplit.symm]
  simp only [Finset.sum_singleton, cglLemma45OffDiagonalNonzeroFrequencyTerm]
  ring

end RHTower
