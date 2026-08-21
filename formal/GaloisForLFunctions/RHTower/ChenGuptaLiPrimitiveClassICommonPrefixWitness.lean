/-
# Chen--Gupta--Li primitive Class-I common-prefix witness

Transfers each existing normalized literal Class-I tail witness to a selected
bounded, zero-padded common-coefficient prefix polynomial.  All denominators
are proven positive from certified source data before division.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassICommonPrefixBlock

open Complex

noncomputable section

namespace RHTower

/-- Canonically selected common-coefficient prefix for one certified Class-I row. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIPrefixIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    Fin (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r + 1) :=
  Classical.choose
    (exists_cglClassIPrefixScaledDetectorPolynomial_weighted_dominates_tail X
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) n χ.1.1
      (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩)

/-- Exact closed domination from the literal normalized tail to its selected
bounded common-coefficient prefix. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixIndex_dominates_tail
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    cglClassIDyadicCoefficientScale X
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) *
        ‖cglShiftedTailDyadicScaledPolynomial X
          (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) n χ.1.1
          (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖ ≤
      cglShiftedTailDyadicCoefficientScale X
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
          cglShiftedTailDyadicRealWeightSequence
            (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
            (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
            ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ 0 *
            ‖cglClassIPrefixScaledDetectorPolynomial X
              (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) n
              (cglPrimitiveClassIWellSpacedClassIPrefixIndex X Y n χ τ H r) χ.1.1
              (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)‖ := by
  exact Classical.choose_spec
    (exists_cglClassIPrefixScaledDetectorPolynomial_weighted_dominates_tail X
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) n χ.1.1
      (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩)

/-- Every selected Class-I dyadic length is positive. -/
theorem cglPrimitiveClassIWellSpacedClassITailLength_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    0 < cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r := by
  unfold cglPrimitiveClassIWellSpacedClassITailLength
  positivity

/-- Initial real weight for every selected Class-I dyadic block is positive. -/
theorem cglPrimitiveClassIWellSpacedClassIInitialWeight_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    0 < cglShiftedTailDyadicRealWeightSequence
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
      (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ 0 := by
  have hN := cglPrimitiveClassIWellSpacedClassITailLength_pos X Y n χ τ H r
  simp only [cglShiftedTailDyadicRealWeightSequence, dif_pos hN]
  unfold cglShiftedTailDyadicRealWeight cglCharacterDyadicIndex
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- Closed numeric threshold for the selected bounded common-coefficient prefix. -/
def cglPrimitiveClassIWellSpacedClassIPrefixThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) : ℝ :=
  cglClassIDyadicCoefficientScale X
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) *
    cglPrimitiveClassIWellSpacedClassITailThreshold X Y n χ τ H r /
      (cglShiftedTailDyadicCoefficientScale X
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
        cglShiftedTailDyadicRealWeightSequence
          (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
          (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ 0)

/-- Every certified Class-I row has its closed prefix threshold attained by a
bounded common-coefficient polynomial. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixThreshold_le_polynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    cglPrimitiveClassIWellSpacedClassIPrefixThreshold X Y n χ τ H r ≤
      ‖cglClassIPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) n
        (cglPrimitiveClassIWellSpacedClassIPrefixIndex X Y n χ τ H r) χ.1.1
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)‖ := by
  have htail : cglPrimitiveClassIWellSpacedClassITailThreshold X Y n χ τ H r ≤
      ‖cglShiftedTailDyadicScaledPolynomial X
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) n χ.1.1
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖ := by
    simpa [cglPrimitiveClassIWellSpacedClassITailRow,
      cglPrimitiveClassIWellSpacedClassITailCoefficients,
      cglShiftedTailDyadicScaledPolynomial] using
      cglPrimitiveClassIWellSpacedClassITailThreshold_le_polynomial X Y n χ τ H r
  have hfull : 0 ≤ cglClassIDyadicCoefficientScale X
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) := by
    unfold cglClassIDyadicCoefficientScale
    positivity
  have hshift : 0 < cglShiftedTailDyadicCoefficientScale X
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
      (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ := by
    unfold cglShiftedTailDyadicCoefficientScale
    positivity
  have hweight := cglPrimitiveClassIWellSpacedClassIInitialWeight_pos X Y n χ τ H r
  have hden : 0 < cglShiftedTailDyadicCoefficientScale X
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
      (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
      cglShiftedTailDyadicRealWeightSequence
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ 0 := mul_pos hshift hweight
  apply (div_le_iff₀ hden).mpr
  have hscaled := mul_le_mul_of_nonneg_left htail hfull
  have hdom := cglPrimitiveClassIWellSpacedClassIPrefixIndex_dominates_tail X Y n χ τ H r
  exact hscaled.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hdom)

end RHTower
