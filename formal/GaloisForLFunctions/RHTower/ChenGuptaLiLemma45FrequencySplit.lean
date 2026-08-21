/-
# Chen--Gupta--Li Lemma 4.5 zero/nonzero frequency split

Constructs summability of CGL's global three-frequency coefficient by finite
induction, then splits the exact trace series at the origin.  The complement
of the singleton origin is the literal source carrier `Z³ \ {0}`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45FrequencyReindex

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The restriction of CGL's global frequency term to the source carrier
`Z³ \ {0}`. -/
def cglLemma45NonzeroFrequencyTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))}) : ℂ :=
  cglLemma45TraceFrequencyTerm w N Q R rows m

/-- The complement-of-singleton carrier used above is exactly the nonzero
triple-frequency condition in the source notation. -/
theorem cglLemma45_nonzeroFrequency_iff
    (m : (ℤ × ℤ) × ℤ) :
    m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ)) ↔ m ≠ 0 := by
  simp

/-- CGL's global three-frequency coefficient is summable.  Its proof is a
finite induction over row/residue indices applied to the closed Schwartz
summability certificate of each fixed index. -/
theorem cglLemma45TraceFrequencyTerm_summable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    Summable (cglLemma45TraceFrequencyTerm w N Q R rows) := by
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
  have hsingle : ∀ i ∈ cglLemma45FrequencyIndex Q R, Summable (f i) := by
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
  change Summable (fun m => ∑ i ∈ cglLemma45FrequencyIndex Q R, f i m)
  exact finiteSum_summable (cglLemma45FrequencyIndex Q R) hsingle

/-- **CGL Lemma 4.5, exact frequency split.** The complete weighted cubic
trace equals its zero-frequency term plus the exact sum over `Z³ \ {0}`.
No error bound, separation premise, or convergence assumption is supplied by
the caller. -/
theorem cglLemma45_cubicTrace_eq_zero_add_nonzeroFrequencySum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglCharacterDyadicWeightedGramCubicTrace N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
      cglLemma45TraceFrequencyTerm w N Q R rows 0 +
        ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45NonzeroFrequencyTerm w N Q R rows m := by
  rw [cglLemma45_cubicTrace_eq_tsum_frequencyTerm]
  have hsum := cglLemma45TraceFrequencyTerm_summable w N Q R rows
  have hsplit := hsum.sum_add_tsum_subtype_compl ({0} : Finset ((ℤ × ℤ) × ℤ))
  simpa [cglLemma45NonzeroFrequencyTerm] using hsplit.symm

end RHTower
