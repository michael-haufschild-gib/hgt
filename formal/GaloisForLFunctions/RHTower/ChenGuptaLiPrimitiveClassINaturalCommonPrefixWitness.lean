/-
# Chen--Gupta--Li coarse Class-I common-prefix witness

Transfers each literal Class-I tail witness in the certified coarse-spaced
primitive packet to a bounded, zero-padded common-coefficient prefix
polynomial.  The construction preserves the original zero and `(K + 1)`
spacing; only the row-dependent real tail weights are removed by Abel
summation.

No RH, GRH, zero-density, large-value, or moment premise is supplied by a
caller.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalHeterogeneousPacket
import GaloisForLFunctions.RHTower.ChenGuptaLiClassICommonPrefixCutoff

open Complex

noncomputable section

namespace RHTower

/-- Canonical bounded common-coefficient prefix selected for one coarse
Class-I row. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPrefixIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    Fin (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r + 1) :=
  Classical.choose
    (exists_cglClassIPrefixScaledDetectorPolynomial_weighted_dominates_tail X
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) n χ.1.1
      (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩)

/-- Exact Abel domination of the normalized coarse tail by its selected
bounded common-coefficient prefix. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixIndex_dominates_tail
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    cglClassIDyadicCoefficientScale X
        (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) *
        ‖cglShiftedTailDyadicScaledPolynomial X
          (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) n χ.1.1
          (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖ ≤
      cglShiftedTailDyadicCoefficientScale X
        (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
          cglShiftedTailDyadicRealWeightSequence
            (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
            (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
            ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ 0 *
            ‖cglClassIPrefixScaledDetectorPolynomial X
              (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) n
              (cglPrimitiveClassINaturalWellSpacedClassIPrefixIndex X Y n χ τ H K r) χ.1.1
              (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)‖ := by
  exact Classical.choose_spec
    (exists_cglClassIPrefixScaledDetectorPolynomial_weighted_dominates_tail X
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) n χ.1.1
      (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩)

/-- Every selected coarse Class-I tail block has positive length. -/
theorem cglPrimitiveClassINaturalWellSpacedClassITailLength_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    0 < cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r := by
  unfold cglPrimitiveClassINaturalWellSpacedClassITailLength
  positivity

/-- Initial literal real tail weight of each coarse Class-I row is positive. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIInitialWeight_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    0 < cglShiftedTailDyadicRealWeightSequence
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
      (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ 0 := by
  have hN := cglPrimitiveClassINaturalWellSpacedClassITailLength_pos X Y n χ τ H K r
  simp only [cglShiftedTailDyadicRealWeightSequence, dif_pos hN]
  unfold cglShiftedTailDyadicRealWeight cglCharacterDyadicIndex
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- Closed positive threshold attained by the selected coarse common-prefix
polynomial. -/
def cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) : ℝ :=
  cglClassIDyadicCoefficientScale X
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) *
    cglPrimitiveClassINaturalWellSpacedClassITailThreshold X Y n χ τ H K r /
      (cglShiftedTailDyadicCoefficientScale X
        (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
        cglShiftedTailDyadicRealWeightSequence
          (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
          (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ 0)

/-- Each coarse Class-I common-prefix threshold is attained by its bounded
common-coefficient polynomial. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold_le_polynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold X Y n χ τ H K r ≤
      ‖cglClassIPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) n
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixIndex X Y n χ τ H K r) χ.1.1
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)‖ := by
  have htail := cglPrimitiveClassINaturalWellSpacedClassITailThreshold_le_polynomial X Y n χ τ H K r
  have hfull : 0 ≤ cglClassIDyadicCoefficientScale X
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) := by
    unfold cglClassIDyadicCoefficientScale
    positivity
  have hshift : 0 < cglShiftedTailDyadicCoefficientScale X
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
      (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ := by
    unfold cglShiftedTailDyadicCoefficientScale
    positivity
  have hweight := cglPrimitiveClassINaturalWellSpacedClassIInitialWeight_pos X Y n χ τ H K r
  have hden : 0 < cglShiftedTailDyadicCoefficientScale X
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
      (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
      cglShiftedTailDyadicRealWeightSequence
        (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ 0 := mul_pos hshift hweight
  apply (div_le_iff₀ hden).mpr
  have hscaled := mul_le_mul_of_nonneg_left htail hfull
  have hdom := cglPrimitiveClassINaturalWellSpacedClassIPrefixIndex_dominates_tail X Y n χ τ H K r
  exact hscaled.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hdom)

/-- Every coarse common-prefix threshold is strictly positive. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    0 < cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold X Y n χ τ H K r := by
  have hfull : 0 < cglClassIDyadicCoefficientScale X
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) := by
    unfold cglClassIDyadicCoefficientScale
    positivity
  have htail : 0 < cglPrimitiveClassINaturalWellSpacedClassITailThreshold X Y n χ τ H K r := by
    unfold cglPrimitiveClassINaturalWellSpacedClassITailThreshold
    have hdepth := cglPrimitiveClassINaturalWellSpacedClassITailDepth_pos X Y n χ τ H K r
    have hscale : 0 < cglShiftedTailDyadicCoefficientScale X
        (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ := by
      unfold cglShiftedTailDyadicCoefficientScale
      positivity
    positivity
  have hshift : 0 < cglShiftedTailDyadicCoefficientScale X
      (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
      (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ := by
    unfold cglShiftedTailDyadicCoefficientScale
    positivity
  have hweight := cglPrimitiveClassINaturalWellSpacedClassIInitialWeight_pos X Y n χ τ H K r
  unfold cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold
  exact div_pos (mul_pos hfull htail) (mul_pos hshift hweight)

/-- Natural cutoff of the canonical coarse common-prefix witness. -/
def cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) : ℕ :=
  (cglPrimitiveClassINaturalWellSpacedClassIPrefixIndex X Y n χ τ H K r).1

/-- The coarse common-prefix threshold is attained by its natural-cutoff
bounded common-coefficient polynomial. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold_le_natPolynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold X Y n χ τ H K r ≤
      ‖cglClassINatPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) n
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff X Y n χ τ H K r) χ.1.1
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)‖ := by
  simpa [cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff,
    cglClassINatPrefixScaledDetectorPolynomial_of_fin] using
    cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold_le_polynomial X Y n χ τ H K r

end RHTower
