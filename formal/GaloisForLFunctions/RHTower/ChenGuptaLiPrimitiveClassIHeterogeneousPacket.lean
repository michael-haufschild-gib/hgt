/-
# Chen--Gupta--Li primitive Class-I heterogeneous packet

The exact current Class-I witness retains the real zero-dependent weights
`n^{-Re rho} exp(-n/Y)`. This module exposes a canonical finite carrier for
those literal witnesses while keeping their varying dyadic lengths and
coefficient vectors explicit. It does not claim the source's later common
coefficient reduction.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassIIPacket

open Complex

noncomputable section

namespace RHTower

noncomputable def cglPrimitiveClassIWellSpacedClassITailDepth
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) : ℕ :=
  Classical.choose (cglPrimitiveClassIWellSpacedClassI_row_spec X Y n χ τ H r)

theorem exists_cglPrimitiveClassIWellSpacedClassITailIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    ∃ j : Fin (cglPrimitiveClassIWellSpacedClassITailDepth X Y n χ τ H r),
      cglShiftedTailDyadicCoefficientScale X (2 ^ j.1)
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassIWellSpacedZero n χ τ H r.1))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
          (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) /
            (4 * (cglPrimitiveClassIWellSpacedClassITailDepth X Y n χ τ H r : ℝ))) ≤
        ‖cglShiftedTailDyadicScaledPolynomial X (2 ^ j.1) n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
            (cglPrimitiveClassIWellSpacedZero n χ τ H r.1))
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖ := by
  exact Classical.choose_spec (cglPrimitiveClassIWellSpacedClassI_row_spec X Y n χ τ H r)

noncomputable def cglPrimitiveClassIWellSpacedClassITailIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    Fin (cglPrimitiveClassIWellSpacedClassITailDepth X Y n χ τ H r) :=
  Classical.choose (exists_cglPrimitiveClassIWellSpacedClassITailIndex X Y n χ τ H r)

theorem cglPrimitiveClassIWellSpacedClassITailIndex_witness
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    cglShiftedTailDyadicCoefficientScale X
        (2 ^ (cglPrimitiveClassIWellSpacedClassITailIndex X Y n χ τ H r).1)
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassIWellSpacedZero n χ τ H r.1))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
          (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) /
            (4 * (cglPrimitiveClassIWellSpacedClassITailDepth X Y n χ τ H r : ℝ))) ≤
      ‖cglShiftedTailDyadicScaledPolynomial X
        (2 ^ (cglPrimitiveClassIWellSpacedClassITailIndex X Y n χ τ H r).1) n χ.1.1
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassIWellSpacedZero n χ τ H r.1))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖ := by
  exact Classical.choose_spec
    (exists_cglPrimitiveClassIWellSpacedClassITailIndex X Y n χ τ H r)

def cglPrimitiveClassIWellSpacedClassITailLength
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) : ℕ :=
  2 ^ (cglPrimitiveClassIWellSpacedClassITailIndex X Y n χ τ H r).1

def cglPrimitiveClassIWellSpacedClassITailPoint
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) : CGLRightHalfPlanePoint :=
  cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
    (cglPrimitiveClassIWellSpacedZero n χ τ H r.1)

def cglPrimitiveClassIWellSpacedClassITailRow
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    CGLCharacterDyadicRowData (n + 1) :=
  cglShiftedTailDyadicRow χ.1.1
    (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)

def cglPrimitiveClassIWellSpacedClassITailCoefficients
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    EuclideanSpace ℂ (Fin (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)) :=
  cglShiftedTailDyadicScaledCoefficients X
    (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
    (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
    ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩

def cglPrimitiveClassIWellSpacedClassITailThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) : ℝ :=
  cglShiftedTailDyadicCoefficientScale X
    (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
    (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
    ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
      (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) /
        (4 * (cglPrimitiveClassIWellSpacedClassITailDepth X Y n χ τ H r : ℝ)))

theorem cglPrimitiveClassIWellSpacedClassITailDepth_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    0 < cglPrimitiveClassIWellSpacedClassITailDepth X Y n χ τ H r := by
  have hlt := (cglPrimitiveClassIWellSpacedClassITailIndex X Y n χ τ H r).isLt
  omega

theorem cglPrimitiveClassIWellSpacedClassITailThreshold_le_polynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    cglPrimitiveClassIWellSpacedClassITailThreshold X Y n χ τ H r ≤
      ‖cglCharacterDyadicPolynomial
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) (n + 1)
        (cglPrimitiveClassIWellSpacedClassITailRow n χ τ H r)
        (cglPrimitiveClassIWellSpacedClassITailCoefficients X Y n χ τ H r)‖ := by
  simpa [cglPrimitiveClassIWellSpacedClassITailThreshold,
    cglPrimitiveClassIWellSpacedClassITailLength,
    cglPrimitiveClassIWellSpacedClassITailPoint,
    cglPrimitiveClassIWellSpacedClassITailRow,
    cglPrimitiveClassIWellSpacedClassITailCoefficients,
    cglShiftedTailDyadicScaledPolynomial] using
      cglPrimitiveClassIWellSpacedClassITailIndex_witness X Y n χ τ H r

theorem norm_cglPrimitiveClassIWellSpacedClassITailCoefficient_le_one
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H)
    (j : Fin (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)) :
    ‖(cglPrimitiveClassIWellSpacedClassITailCoefficients X Y n χ τ H r) j‖ ≤ 1 := by
  exact norm_cglShiftedTailDyadicScaledCoefficient_le_one X
    (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
    (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
    ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ j

noncomputable def cglPrimitiveClassIWellSpacedClassIPacketIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H :=
  (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).equivFin.symm i

def cglPrimitiveClassIWellSpacedClassIPacketTailLength
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) : ℕ :=
  cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)

def cglPrimitiveClassIWellSpacedClassIPacketTailRow
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    CGLCharacterDyadicRowData (n + 1) :=
  cglPrimitiveClassIWellSpacedClassITailRow n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)

def cglPrimitiveClassIWellSpacedClassIPacketTailCoefficients
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    EuclideanSpace ℂ (Fin (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i)) :=
  cglPrimitiveClassIWellSpacedClassITailCoefficients X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)

theorem cglPrimitiveClassIWellSpacedClassIPacketTailThreshold_le_polynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    cglPrimitiveClassIWellSpacedClassITailThreshold X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i) ≤
      ‖cglCharacterDyadicPolynomial
        (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i) (n + 1)
        (cglPrimitiveClassIWellSpacedClassIPacketTailRow X Y n χ τ H i)
        (cglPrimitiveClassIWellSpacedClassIPacketTailCoefficients X Y n χ τ H i)‖ := by
  exact cglPrimitiveClassIWellSpacedClassITailThreshold_le_polynomial X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)

end RHTower
