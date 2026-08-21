/-
# Chen--Gupta--Li primitive well-spaced zero rows

This module makes the finite primitive zero packet underlying the CGL
Class-I branch literal.  It chooses the already-certified unit-separated
subpacket of the actual multiplicity-aware zero-copy packet, then retains
exactly the rows lying strictly right of the critical line.  Every retained
row carries its actual primitive zero and therefore the closed normalized
dyadic Class-I witness.

No RH, GRH, zero-density, zero-detection, local-capacity, or large-value
premise is supplied by callers.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassINormalizedDyadicWitness
import GaloisForLFunctions.RHTower.DirichletLZeroDensityWindowRows

noncomputable section

namespace RHTower

/-- The canonical unit-separated selection from the finite multiplicity-copy
zero packet for one primitive nonprincipal character. -/
noncomputable def cglPrimitiveClassIWindowWellSpacedSelection
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ.1 (1 / 2) τ H)) :=
  Classical.choose (exists_cglZeroDensityVerticalWindowSelectedRows_unit_wellSpaced_count
    (n := n) (χ := χ.1) (σ := (1 / 2 : ℝ)) (τ := τ) (H := H))

/-- The canonical separated selection controls the literal
multiplicity-weighted zero count with its closed finite capacity loss. -/
theorem cglPrimitiveClassIWindowWellSpacedSelection_count
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    completedLFunctionZeroDensityVerticalWindowCount n χ.1 (1 / 2) τ H ≤
      (2 * cglZeroDensityVerticalWindowCopyCard n χ.1 (1 / 2) τ H *
        (cglPrimitiveClassIWindowWellSpacedSelection n χ τ H).card : ℕ) := by
  exact (Classical.choose_spec
    (exists_cglZeroDensityVerticalWindowSelectedRows_unit_wellSpaced_count
      (n := n) (χ := χ.1) (σ := (1 / 2 : ℝ)) (τ := τ) (H := H))).1

/-- Rows in the canonical selection remain unit-separated. -/
theorem cglPrimitiveClassIWindowWellSpacedSelection_separated
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r s : Fin (Fintype.card (↑(cglPrimitiveClassIWindowWellSpacedSelection n χ τ H))))
    (hrs : r ≠ s) :
    (1 : ℝ) ≤
      |(cglZeroDensityVerticalWindowSelectedRows n χ.1 (1 / 2) τ H
        (cglPrimitiveClassIWindowWellSpacedSelection n χ τ H) r).time -
        (cglZeroDensityVerticalWindowSelectedRows n χ.1 (1 / 2) τ H
          (cglPrimitiveClassIWindowWellSpacedSelection n χ τ H) s).time| := by
  exact (Classical.choose_spec
    (exists_cglZeroDensityVerticalWindowSelectedRows_unit_wellSpaced_count
      (n := n) (χ := χ.1) (σ := (1 / 2 : ℝ)) (τ := τ) (H := H))).2 r s hrs

/-- A row of the selected packet whose actual zero lies strictly right of the
critical line.  The inequality is certified in the row index rather than
supplied as a theorem premise. -/
def CGLPrimitiveClassIWellSpacedIndex
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :=
  {r : Fin (Fintype.card (↑(cglPrimitiveClassIWindowWellSpacedSelection n χ τ H))) //
    (1 / 2 : ℝ) <
      (cglZeroDensityVerticalWindowSelectedRowsPoint n χ.1 (1 / 2) τ H
        (cglPrimitiveClassIWindowWellSpacedSelection n χ τ H) r).1.re}

/-- The CGL character/ordinate row carried by a right-of-critical-line
primitive zero in the canonical selected packet. -/
def cglPrimitiveClassIWellSpacedRow
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedIndex n χ τ H) : CGLCharacterDyadicRowData (n + 1) :=
  cglZeroDensityVerticalWindowSelectedRows n χ.1 (1 / 2) τ H
    (cglPrimitiveClassIWindowWellSpacedSelection n χ τ H) r.1

/-- The exact primitive Class-I zero retained by one selected row. -/
def cglPrimitiveClassIWellSpacedZero
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedIndex n χ τ H) :
    CGLPrimitiveClassIWindowZero n χ τ H :=
  ⟨cglZeroDensityVerticalWindowSelectedRowsPoint n χ.1 (1 / 2) τ H
    (cglPrimitiveClassIWindowWellSpacedSelection n χ τ H) r.1, r.2⟩

/-- Each selected Class-I row has the original primitive character. -/
theorem cglPrimitiveClassIWellSpacedRow_character
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedIndex n χ τ H) :
    (cglPrimitiveClassIWellSpacedRow n χ τ H r).character = χ.1.1 := by
  rfl

/-- The zero ordinate agrees exactly with the time carried by its CGL row. -/
theorem cglPrimitiveClassIWellSpacedZero_im_eq_row_time
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedIndex n χ τ H) :
    (cglPrimitiveClassIWellSpacedZero n χ τ H r).1.1.im =
      (cglPrimitiveClassIWellSpacedRow n χ τ H r).time := by
  rfl

/-- The Class-I eligible subpacket inherits unit separation from the canonical
selection. -/
theorem cglPrimitiveClassIWellSpacedRows_separated
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r s : CGLPrimitiveClassIWellSpacedIndex n χ τ H) (hrs : r ≠ s) :
    (1 : ℝ) ≤ |(cglPrimitiveClassIWellSpacedRow n χ τ H r).time -
      (cglPrimitiveClassIWellSpacedRow n χ τ H s).time| := by
  apply cglPrimitiveClassIWindowWellSpacedSelection_separated n χ τ H r.1 s.1
  intro h
  exact hrs (Subtype.ext h)

/-- **Chen--Gupta--Li, Section 12.1--12.3:** every row in the canonical
primitive, well-spaced Class-I carrier forces the exact normalized dyadic
character-polynomial witness or the remaining source critical-line Mellin
integral alternative. -/
theorem cglPrimitiveClassIWellSpacedRow_normalizedDyadicWitness
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedIndex n χ τ H) :
    (∃ L : ℕ, ∃ j : Fin L,
      cglShiftedTailDyadicCoefficientScale X (2 ^ j.1)
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassIWellSpacedZero n χ τ H r))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
          (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ))) ≤
        ‖cglShiftedTailDyadicScaledPolynomial X (2 ^ j.1) n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
            (cglPrimitiveClassIWellSpacedZero n χ τ H r))
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖) ∨
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 2 ≤
        ‖(1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H
              (cglPrimitiveClassIWellSpacedZero n χ τ H r)).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * Complex.I))‖ := by
  exact cglPrimitiveClassI_normalizedDyadicBlock_or_safeLineIntegral_large X n Y χ τ H
    (cglPrimitiveClassIWellSpacedZero n χ τ H r)

end RHTower
