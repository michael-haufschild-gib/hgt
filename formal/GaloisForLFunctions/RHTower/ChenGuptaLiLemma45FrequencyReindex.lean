/-
# Chen--Gupta--Li Lemma 4.5 frequency reindexing

Packages CGL's finite row/residue factors into one finite frequency index and
uses the derived Schwartz certificates to commute that finite sum with the
three-dimensional frequency series.  This produces the source-form global
frequency term `I_m` without an assumed Fubini condition.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45TracePoisson

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The finite row/residue carrier for CGL Lemma 4.5's global frequency term. -/
def cglLemma45FrequencyIndex (Q : CGLPositiveModulus) (R : ℕ) :
    Finset ((((Fin R × Fin R × Fin R) × ZMod Q.value) × ZMod Q.value) × ZMod Q.value) :=
  (((cglCharacterDyadicGramCubicIndexSet R ×ˢ Finset.univ) ×ˢ Finset.univ) ×ˢ
    Finset.univ)

/-- CGL's complete finite row/residue coefficient at one triple frequency. -/
def cglLemma45TraceFrequencyTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) (m : (ℤ × ℤ) × ℤ) : ℂ :=
  ∑ i ∈ cglLemma45FrequencyIndex Q R,
    cglLemma45TripleFrequencyTerm w N Q
      (rows i.1.1.1.1).character (rows i.1.1.1.2.1).character
      (rows i.1.1.1.2.1).character (rows i.1.1.1.2.2).character
      (rows i.1.1.1.2.2).character (rows i.1.1.1.1).character
      ((rows i.1.1.1.1).time - (rows i.1.1.1.2.1).time)
      ((rows i.1.1.1.2.1).time - (rows i.1.1.1.2.2).time)
      ((rows i.1.1.1.2.2).time - (rows i.1.1.1.1).time)
      i.1.1.2 i.1.2 i.2 m

/-- **CGL Lemma 4.5, global frequency reindexing.** The weighted cubic Gram
trace equals the source-form sum over its global `Z³` frequency terms.  The
only finite/infinite interchange is discharged by constructed absolute
summability certificates. -/
theorem cglLemma45_cubicTrace_eq_tsum_frequencyTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglCharacterDyadicWeightedGramCubicTrace N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
      ∑' m : (ℤ × ℤ) × ℤ, cglLemma45TraceFrequencyTerm w N Q R rows m := by
  let s := cglLemma45FrequencyIndex Q R
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
    cglCharacterDyadicWeightedGramCubicTrace N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
        ∑ i ∈ s, ∑' m : (ℤ × ℤ) × ℤ, f i m := by
      rw [cglLemma45_cubicTrace_eq_threeFrequencySums]
      dsimp only [s, f, cglLemma45FrequencyIndex]
      rw [Finset.sum_product, Finset.sum_product, Finset.sum_product]
    _ = ∑' m : (ℤ × ℤ) × ℤ, ∑ i ∈ s, f i m := hswap.symm
    _ = ∑' m : (ℤ × ℤ) × ℤ, cglLemma45TraceFrequencyTerm w N Q R rows m := by
      rfl

end RHTower
