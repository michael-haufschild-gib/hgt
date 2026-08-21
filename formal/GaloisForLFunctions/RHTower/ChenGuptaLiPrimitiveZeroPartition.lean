/-
# Chen--Gupta--Li primitive zero-row partition

For the canonical finite primitive well-spaced packet, this module makes the
tail-versus-left-critical-line dichotomy literal. Class I is the exact
normalized dyadic tail witness; its complement is certified to carry a finite
left critical-line Mellin-integral witness. The source's sharper logarithmic
truncation and local L-value lower bound remain separate analytic steps.

No RH, GRH, zero-density, zero-detection, local-capacity, large-value, or
moment premise is supplied by callers.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILeftWitness

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-- The normalized finite dyadic character-polynomial alternative for one
primitive, selected, well-spaced zero row. -/
def cglPrimitiveClassIWellSpacedTailWitness
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedIndex n χ τ H) : Prop :=
  ∃ L : ℕ, ∃ j : Fin L,
    cglShiftedTailDyadicCoefficientScale X (2 ^ j.1)
      (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
        (cglPrimitiveClassIWellSpacedZero n χ τ H r))
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
        (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ))) ≤
      ‖cglShiftedTailDyadicScaledPolynomial X (2 ^ j.1) n χ.1.1
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassIWellSpacedZero n χ τ H r))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖

/-- The finite source left critical-line Mellin-integral alternative for one
primitive, selected, well-spaced zero row. -/
def cglPrimitiveClassIWellSpacedLeftLineWitness
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedIndex n χ τ H) : Prop :=
  ∃ K : ℕ, Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
    ‖(1 / (2 * Real.pi) : ℝ) •
      (∫ t in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H
            (cglPrimitiveClassIWellSpacedZero n χ τ H r)).toCGLNonprincipalCriticalStripLZero
          ((((1 / 2 : ℝ) -
            (cglPrimitiveClassIWellSpacedZero n χ τ H r).1.1.re : ℝ) : ℂ) +
              (t : ℂ) * I))‖

/-- Every selected primitive row has the exact CGL Class-I dyadic witness or
the finite left critical-line witness underlying the Class-II branch. -/
theorem cglPrimitiveClassIWellSpaced_tail_or_leftLine
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedIndex n χ τ H) :
    cglPrimitiveClassIWellSpacedTailWitness X Y n χ τ H r ∨
      cglPrimitiveClassIWellSpacedLeftLineWitness X Y n χ τ H r := by
  simpa only [cglPrimitiveClassIWellSpacedTailWitness,
    cglPrimitiveClassIWellSpacedLeftLineWitness] using
    cglPrimitiveClassI_normalizedDyadicBlock_or_exists_leftLineIntegral_large X n Y χ τ H
      (cglPrimitiveClassIWellSpacedZero n χ τ H r)

/-- Explicit finite enumeration of every Class-I-eligible row in the selected
primitive packet. -/
noncomputable def cglPrimitiveClassIWellSpacedAllRows
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    Finset (CGLPrimitiveClassIWellSpacedIndex n χ τ H) := by
  classical
  letI : Fintype (CGLPrimitiveClassIWellSpacedIndex n χ τ H) :=
    Fintype.subtype
      ((Finset.univ : Finset (Fin (Fintype.card
        (↑(cglPrimitiveClassIWindowWellSpacedSelection n χ τ H))))).filter fun r =>
          (1 / 2 : ℝ) <
            (cglZeroDensityVerticalWindowSelectedRowsPoint n χ.1 (1 / 2) τ H
              (cglPrimitiveClassIWindowWellSpacedSelection n χ τ H) r).1.re)
      (by simp)
  exact Finset.univ

/-- The canonical source Class-I subpacket: rows with a normalized dyadic
tail witness. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIRows
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    Finset (CGLPrimitiveClassIWellSpacedIndex n χ τ H) := by
  classical
  exact (cglPrimitiveClassIWellSpacedAllRows n χ τ H).filter
    (cglPrimitiveClassIWellSpacedTailWitness X Y n χ τ H)

/-- The canonical left-critical-line subpacket: complement of the normalized
dyadic tail-witness packet. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIIRows
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    Finset (CGLPrimitiveClassIWellSpacedIndex n χ τ H) := by
  classical
  exact (cglPrimitiveClassIWellSpacedAllRows n χ τ H).filter fun r =>
    ¬ cglPrimitiveClassIWellSpacedTailWitness X Y n χ τ H r

/-- A row in the finite Class-I subpacket, carrying its witness certificate. -/
abbrev CGLPrimitiveClassIWellSpacedClassIRow
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :=
  ↑(cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H)

/-- A row in the finite left-critical-line subpacket, carrying its
complementary certificate. -/
abbrev CGLPrimitiveClassIWellSpacedClassIIRow
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :=
  ↑(cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H)

/-- Each finite Class-I row carries the exact normalized dyadic witness. -/
theorem cglPrimitiveClassIWellSpacedClassI_row_spec
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    cglPrimitiveClassIWellSpacedTailWitness X Y n χ τ H r.1 := by
  classical
  exact (Finset.mem_filter.mp r.2).2

/-- Each finite complementary row carries the finite left critical-line
Mellin-integral witness. -/
theorem cglPrimitiveClassIWellSpacedClassII_row_leftLine
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    cglPrimitiveClassIWellSpacedLeftLineWitness X Y n χ τ H r.1 := by
  classical
  rcases cglPrimitiveClassIWellSpaced_tail_or_leftLine X Y n χ τ H r.1 with htail | hsafe
  · exact False.elim ((Finset.mem_filter.mp r.2).2 htail)
  · exact hsafe

/-- The two canonical subpackets partition the explicitly enumerated finite
primitive zero-row carrier. -/
theorem cglPrimitiveClassIWellSpacedClass_rows_card
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card +
      (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card =
        (cglPrimitiveClassIWellSpacedAllRows n χ τ H).card := by
  classical
  simpa only [cglPrimitiveClassIWellSpacedClassIRows,
    cglPrimitiveClassIWellSpacedClassIIRows] using
    (Finset.card_filter_add_card_filter_not
      (s := (cglPrimitiveClassIWellSpacedAllRows n χ τ H))
      (cglPrimitiveClassIWellSpacedTailWitness X Y n χ τ H))

end RHTower
