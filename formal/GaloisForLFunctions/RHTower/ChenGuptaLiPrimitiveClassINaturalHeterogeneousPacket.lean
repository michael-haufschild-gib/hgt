/-
# Chen--Gupta--Li coarse Class-I heterogeneous packet

This module extracts the literal tail witness from every Class-I row in the
certified `(K + 1)`-separated primitive zero packet.  Its dyadic length and
weighted coefficients can vary by row; the later common-prefix reduction will
remove precisely that variation without changing the coarse zero carrier.

No RH, GRH, zero-density, large-value, or moment premise is supplied by a
caller.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalPartition

open Complex

noncomputable section

namespace RHTower

/-- Depth of the exact normalized dyadic-tail alternative selected for one
coarse Class-I row. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassITailDepth
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) : ℕ :=
  Classical.choose (cglPrimitiveClassINaturalWellSpacedClassI_row_spec X Y n χ τ H K r)

/-- The selected coarse Class-I tail depth has a dyadic block meeting the
literal normalized tail threshold. -/
theorem exists_cglPrimitiveClassINaturalWellSpacedClassITailIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    ∃ j : Fin (cglPrimitiveClassINaturalWellSpacedClassITailDepth X Y n χ τ H K r),
      cglShiftedTailDyadicCoefficientScale X (2 ^ j.1)
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r.1))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
          (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) /
            (4 * (cglPrimitiveClassINaturalWellSpacedClassITailDepth X Y n χ τ H K r : ℝ))) ≤
        ‖cglShiftedTailDyadicScaledPolynomial X (2 ^ j.1) n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
            (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r.1))
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖ := by
  exact Classical.choose_spec
    (cglPrimitiveClassINaturalWellSpacedClassI_row_spec X Y n χ τ H K r)

/-- Canonical dyadic tail block selected for one coarse Class-I row. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassITailIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    Fin (cglPrimitiveClassINaturalWellSpacedClassITailDepth X Y n χ τ H K r) :=
  Classical.choose
    (exists_cglPrimitiveClassINaturalWellSpacedClassITailIndex X Y n χ τ H K r)

/-- Exact large-value witness for the canonical coarse Class-I dyadic block. -/
theorem cglPrimitiveClassINaturalWellSpacedClassITailIndex_witness
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    cglShiftedTailDyadicCoefficientScale X
        (2 ^ (cglPrimitiveClassINaturalWellSpacedClassITailIndex X Y n χ τ H K r).1)
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r.1))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
          (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) /
            (4 * (cglPrimitiveClassINaturalWellSpacedClassITailDepth X Y n χ τ H K r : ℝ))) ≤
      ‖cglShiftedTailDyadicScaledPolynomial X
        (2 ^ (cglPrimitiveClassINaturalWellSpacedClassITailIndex X Y n χ τ H K r).1) n χ.1.1
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r.1))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖ := by
  exact Classical.choose_spec
    (exists_cglPrimitiveClassINaturalWellSpacedClassITailIndex X Y n χ τ H K r)

/-- Dyadic length of the canonical coarse Class-I tail block. -/
def cglPrimitiveClassINaturalWellSpacedClassITailLength
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) : ℕ :=
  2 ^ (cglPrimitiveClassINaturalWellSpacedClassITailIndex X Y n χ τ H K r).1

/-- Right-half-plane point associated to one coarse Class-I tail block. -/
def cglPrimitiveClassINaturalWellSpacedClassITailPoint
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) : CGLRightHalfPlanePoint :=
  cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
    (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r.1)

/-- Literal lower threshold from the selected normalized coarse Class-I tail. -/
def cglPrimitiveClassINaturalWellSpacedClassITailThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) : ℝ :=
  cglShiftedTailDyadicCoefficientScale X
    (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r)
    (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
    ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
      (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) /
        (4 * (cglPrimitiveClassINaturalWellSpacedClassITailDepth X Y n χ τ H K r : ℝ)))

/-- Every selected coarse Class-I dyadic depth is positive. -/
theorem cglPrimitiveClassINaturalWellSpacedClassITailDepth_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    0 < cglPrimitiveClassINaturalWellSpacedClassITailDepth X Y n χ τ H K r := by
  have hlt := (cglPrimitiveClassINaturalWellSpacedClassITailIndex X Y n χ τ H K r).isLt
  omega

/-- The literal lower threshold is attained by its selected weighted dyadic
Dirichlet polynomial. -/
theorem cglPrimitiveClassINaturalWellSpacedClassITailThreshold_le_polynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    cglPrimitiveClassINaturalWellSpacedClassITailThreshold X Y n χ τ H K r ≤
      ‖cglShiftedTailDyadicScaledPolynomial X
        (cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K r) n χ.1.1
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖ := by
  simpa [cglPrimitiveClassINaturalWellSpacedClassITailThreshold,
    cglPrimitiveClassINaturalWellSpacedClassITailLength,
    cglPrimitiveClassINaturalWellSpacedClassITailPoint] using
      cglPrimitiveClassINaturalWellSpacedClassITailIndex_witness X Y n χ τ H K r

end RHTower
