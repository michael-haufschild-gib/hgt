/-
# Chen--Gupta--Li Lemma 4.5 trace Poisson assembly

Lifts the exact rowwise three-frequency identity to the finite cubic Gram
trace.  This is CGL's literal three-Poisson expansion before separating the
zero frequency and the nonzero-frequency error sum.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45CubicPoisson

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- **CGL Lemma 4.5, trace-level Poisson identity.** The literal weighted
cubic Gram trace is the finite row/residue sum of its exact `Z³` frequency
series.  Every inner series is already absolutely summable by construction. -/
theorem cglLemma45_cubicTrace_eq_threeFrequencySums
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglCharacterDyadicWeightedGramCubicTrace N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
      ∑ rst ∈ cglCharacterDyadicGramCubicIndexSet R,
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
  rw [cglCharacterDyadicWeightedGramCubicTrace_eq_cubeSum]
  apply Finset.sum_congr rfl
  intro rst hrst
  exact cglLemma45_cubicRow_eq_threeFrequencySum w N Q R rows rst

end RHTower
