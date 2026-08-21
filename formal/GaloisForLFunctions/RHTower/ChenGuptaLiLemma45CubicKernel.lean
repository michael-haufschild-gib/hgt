/-
# Chen--Gupta--Li Lemma 4.5 cubic kernel normalization

Expands the finite cubic Gram trace at the exact point where CGL cancels its
three dyadic scale phases.  The resulting six-label summand contains precisely
the three normalized `h_t` kernels on which Lemma 4.5 applies Poisson summation.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45EntryKernel
import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedCubicTrace

noncomputable section

namespace RHTower

/-- The normalized six-label kernel after CGL's three dyadic scale phases have
cancelled around a cubic trace. -/
def cglLemma45NormalizedCubicKernelTerm (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (q R : ℕ) (rows : Fin R → CGLCharacterDyadicRowData q)
    (rst : Fin R × Fin R × Fin R) (j₁ j₂ j₃ : Fin N.value) : ℂ :=
  (rows rst.1).character (cglCharacterDyadicIndex N.value j₁) *
      (starRingEnd ℂ) ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j₁)) *
      cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.1).time - (rows rst.2.1).time)
        ((cglCharacterDyadicIndex N.value j₁ : ℝ) / N.value) *
    ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j₂) *
      (starRingEnd ℂ) ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j₂)) *
      cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.2.1).time - (rows rst.2.2).time)
        ((cglCharacterDyadicIndex N.value j₂ : ℝ) / N.value)) *
    ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j₃) *
      (starRingEnd ℂ) ((rows rst.1).character (cglCharacterDyadicIndex N.value j₃)) *
      cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.2.2).time - (rows rst.1).time)
        ((cglCharacterDyadicIndex N.value j₃ : ℝ) / N.value))

/-- **CGL Lemma 4.5, finite cubic normalization.** A literal expanded matrix
summand equals the product of its three normalized Mellin kernels; all
`N^(i(t_r-t_s))` factors cancel exactly. -/
theorem cglCharacterDyadicWeightedGramCubicExpandedTerm_eq_normalizedKernel
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (q R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData q)
    (rst : Fin R × Fin R × Fin R) (j₁ j₂ j₃ : Fin N.value) :
    cglCharacterDyadicWeightedGramCubicExpandedTerm N.value q R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows rst j₁ j₂ j₃ =
      cglLemma45NormalizedCubicKernelTerm w N q R rows rst j₁ j₂ j₃ := by
  have hcycle := cglMellinPhase_cyclic_difference_product N
    (rows rst.1).time (rows rst.2.1).time (rows rst.2.2).time
  unfold cglCharacterDyadicWeightedGramCubicExpandedTerm cglLemma45NormalizedCubicKernelTerm
  calc
    _ =
        ((cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j₁ *
            (starRingEnd ℂ) (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j₁) *
              cglCharacterDyadicPhase N.value ((rows rst.1).time - (rows rst.2.1).time) j₁) *
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j₂ *
            (starRingEnd ℂ) (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j₂) *
              cglCharacterDyadicPhase N.value ((rows rst.2.1).time - (rows rst.2.2).time) j₂) *
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j₃ *
            (starRingEnd ℂ) (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j₃) *
              cglCharacterDyadicPhase N.value ((rows rst.2.2).time - (rows rst.1).time) j₃)) *
        (((rows rst.1).character (cglCharacterDyadicIndex N.value j₁) *
            (starRingEnd ℂ) ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j₁))) *
          ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j₂) *
            (starRingEnd ℂ) ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j₂))) *
          ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j₃) *
            (starRingEnd ℂ) ((rows rst.1).character (cglCharacterDyadicIndex N.value j₃)))) := by ring
    _ =
        ((cglMellinPhase ((rows rst.1).time - (rows rst.2.1).time) N.value *
            cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.1).time - (rows rst.2.1).time)
              ((cglCharacterDyadicIndex N.value j₁ : ℝ) / N.value)) *
          (cglMellinPhase ((rows rst.2.1).time - (rows rst.2.2).time) N.value *
            cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.2.1).time - (rows rst.2.2).time)
              ((cglCharacterDyadicIndex N.value j₂ : ℝ) / N.value)) *
          (cglMellinPhase ((rows rst.2.2).time - (rows rst.1).time) N.value *
            cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.2.2).time - (rows rst.1).time)
              ((cglCharacterDyadicIndex N.value j₃ : ℝ) / N.value))) *
        (((rows rst.1).character (cglCharacterDyadicIndex N.value j₁) *
            (starRingEnd ℂ) ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j₁))) *
          ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j₂) *
            (starRingEnd ℂ) ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j₂))) *
          ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j₃) *
            (starRingEnd ℂ) ((rows rst.1).character (cglCharacterDyadicIndex N.value j₃)))) := by
      rw [cglRealSmoothBumpDyadicWeight_phase_eq_scale_mul_ht,
        cglRealSmoothBumpDyadicWeight_phase_eq_scale_mul_ht,
        cglRealSmoothBumpDyadicWeight_phase_eq_scale_mul_ht]
    _ =
        (cglMellinPhase ((rows rst.1).time - (rows rst.2.1).time) N.value *
          cglMellinPhase ((rows rst.2.1).time - (rows rst.2.2).time) N.value *
            cglMellinPhase ((rows rst.2.2).time - (rows rst.1).time) N.value) *
        (cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.1).time - (rows rst.2.1).time)
            ((cglCharacterDyadicIndex N.value j₁ : ℝ) / N.value) *
          cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.2.1).time - (rows rst.2.2).time)
            ((cglCharacterDyadicIndex N.value j₂ : ℝ) / N.value) *
          cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.2.2).time - (rows rst.1).time)
            ((cglCharacterDyadicIndex N.value j₃ : ℝ) / N.value)) *
        (((rows rst.1).character (cglCharacterDyadicIndex N.value j₁) *
            (starRingEnd ℂ) ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j₁))) *
          ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j₂) *
            (starRingEnd ℂ) ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j₂))) *
          ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j₃) *
            (starRingEnd ℂ) ((rows rst.1).character (cglCharacterDyadicIndex N.value j₃)))) := by ring
    _ = _ := by rw [hcycle]; ring

end RHTower
