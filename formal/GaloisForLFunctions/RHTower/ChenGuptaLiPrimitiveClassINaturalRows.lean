/-
# Chen--Gupta--Li primitive Class-I rows at natural spacing

This is the coarse-spacing counterpart of the canonical unit-spaced primitive
zero carrier.  Starting from the closed `(K+1)`-separated selector, it retains
actual primitive zeros strictly right of the critical line and their literal
Chen--Gupta--Li character/ordinate rows.

No RH, GRH, zero-density, local-capacity, or large-value premise is supplied
by a caller.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityNaturalSpacing
import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassIContours

noncomputable section

namespace RHTower

/-- An actual selected zero strictly right of the critical line in the closed
natural-scale spaced packet. -/
def CGLPrimitiveClassINaturalWellSpacedIndex
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :=
  {r : Fin (Fintype.card
    (↑(cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ.1 (1 / 2) τ H K))) //
    (1 / 2 : ℝ) <
      (cglZeroDensityVerticalWindowSelectedRowsPoint n χ.1 (1 / 2) τ H
        (cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ.1 (1 / 2) τ H K) r).1.re}

/-- The literal CGL character/ordinate row of a natural-scale selected zero. -/
def cglPrimitiveClassINaturalWellSpacedRow
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) : CGLCharacterDyadicRowData (n + 1) :=
  cglZeroDensityVerticalWindowSelectedRows n χ.1 (1 / 2) τ H
    (cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ.1 (1 / 2) τ H K) r.1

/-- The exact primitive Class-I zero retained by a natural-scale selected row. -/
def cglPrimitiveClassINaturalWellSpacedZero
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) :
    CGLPrimitiveClassIWindowZero n χ τ H :=
  ⟨cglZeroDensityVerticalWindowSelectedRowsPoint n χ.1 (1 / 2) τ H
    (cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ.1 (1 / 2) τ H K) r.1, r.2⟩

/-- Every natural-scale selected row retains its source primitive character. -/
theorem cglPrimitiveClassINaturalWellSpacedRow_character
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) :
    (cglPrimitiveClassINaturalWellSpacedRow n χ τ H K r).character = χ.1.1 := by
  rfl

/-- The exact zero ordinate equals the ordinate stored in its character row. -/
theorem cglPrimitiveClassINaturalWellSpacedZero_im_eq_row_time
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) :
    (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r).1.1.im =
      (cglPrimitiveClassINaturalWellSpacedRow n χ τ H K r).time := by
  rfl

/-- Natural-scale Class-I rows retain the closed `(K+1)` ordinate spacing. -/
theorem cglPrimitiveClassINaturalWellSpacedRows_separated
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r s : CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) (hrs : r ≠ s) :
    (K + 1 : ℕ) ≤ |(cglPrimitiveClassINaturalWellSpacedRow n χ τ H K r).time -
      (cglPrimitiveClassINaturalWellSpacedRow n χ τ H K s).time| := by
  apply cglZeroDensityVerticalWindowNaturalWellSpacedSelection_separated n χ.1 (1 / 2) τ H K r.1 s.1
  intro h
  exact hrs (Subtype.ext h)

end RHTower
