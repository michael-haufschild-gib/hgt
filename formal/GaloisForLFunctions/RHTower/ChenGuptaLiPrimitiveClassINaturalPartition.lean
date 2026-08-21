/-
# Chen--Gupta--Li primitive Class-I partition at natural spacing

For CGL's coarse-spacing branch, this module splits every finite
`(K + 1)`-separated primitive zero row into the literal normalized dyadic-tail
branch and its finite left-critical-line Mellin-integral complement.  Both
branches use the same actual zeros and retain the certified source spacing.

No RH, GRH, zero-density, zero-detection, large-value, or moment premise is
supplied by a caller.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalRows
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILeftWitness

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-- The normalized finite dyadic character-polynomial alternative for one
primitive zero from the natural-scale selected packet. -/
def cglPrimitiveClassINaturalWellSpacedTailWitness
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) : Prop :=
  ∃ L : ℕ, ∃ j : Fin L,
    cglShiftedTailDyadicCoefficientScale X (2 ^ j.1)
      (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
        (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r))
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
        (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ))) ≤
      ‖cglShiftedTailDyadicScaledPolynomial X (2 ^ j.1) n χ.1.1
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H
          (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r))
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖

/-- The finite source left-critical-line Mellin-integral alternative for one
primitive zero from the natural-scale selected packet. -/
def cglPrimitiveClassINaturalWellSpacedLeftLineWitness
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) : Prop :=
  ∃ M : ℕ, Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
    ‖(1 / (2 * Real.pi) : ℝ) •
      (∫ t in (-((M + 1 : ℕ) : ℝ))..((M + 1 : ℕ) : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H
            (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r)).toCGLNonprincipalCriticalStripLZero
          ((((1 / 2 : ℝ) -
            (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r).1.1.re : ℝ) : ℂ) +
              (t : ℂ) * I))‖

/-- Each natural-scale selected primitive zero has the source normalized
dyadic-tail witness or the finite left-critical-line witness. -/
theorem cglPrimitiveClassINaturalWellSpaced_tail_or_leftLine
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) :
    cglPrimitiveClassINaturalWellSpacedTailWitness X Y n χ τ H K r ∨
      cglPrimitiveClassINaturalWellSpacedLeftLineWitness X Y n χ τ H K r := by
  simpa only [cglPrimitiveClassINaturalWellSpacedTailWitness,
    cglPrimitiveClassINaturalWellSpacedLeftLineWitness] using
    cglPrimitiveClassI_normalizedDyadicBlock_or_exists_leftLineIntegral_large X n Y χ τ H
      (cglPrimitiveClassINaturalWellSpacedZero n χ τ H K r)

/-- Explicit finite enumeration of every right-of-critical-line row in the
natural-scale primitive zero packet. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedAllRows
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :
    Finset (CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) := by
  classical
  letI : Fintype (CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) :=
    Fintype.subtype
      ((Finset.univ : Finset (Fin (Fintype.card
        (↑(cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ.1 (1 / 2) τ H K))))).filter fun r =>
          (1 / 2 : ℝ) <
            (cglZeroDensityVerticalWindowSelectedRowsPoint n χ.1 (1 / 2) τ H
              (cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ.1 (1 / 2) τ H K) r).1.re)
      (by simp)
  exact Finset.univ

/-- The natural-spacing CGL Class-I subpacket: rows with a normalized dyadic
tail witness. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIRows
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :
    Finset (CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) := by
  classical
  exact (cglPrimitiveClassINaturalWellSpacedAllRows n χ τ H K).filter
    (cglPrimitiveClassINaturalWellSpacedTailWitness X Y n χ τ H K)

/-- The natural-spacing CGL Class-II subpacket: rows not in the dyadic-tail
branch. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIIRows
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :
    Finset (CGLPrimitiveClassINaturalWellSpacedIndex n χ τ H K) := by
  classical
  exact (cglPrimitiveClassINaturalWellSpacedAllRows n χ τ H K).filter fun r =>
    ¬ cglPrimitiveClassINaturalWellSpacedTailWitness X Y n χ τ H K r

/-- A natural-spacing Class-I row carrying its normalized dyadic-tail
certificate. -/
abbrev CGLPrimitiveClassINaturalWellSpacedClassIRow
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :=
  ↑(cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K)

/-- A natural-spacing Class-II row carrying its left-line certificate. -/
abbrev CGLPrimitiveClassINaturalWellSpacedClassIIRow
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :=
  ↑(cglPrimitiveClassINaturalWellSpacedClassIIRows X Y n χ τ H K)

/-- Each finite natural-spacing Class-I row has the exact normalized dyadic
tail witness. -/
theorem cglPrimitiveClassINaturalWellSpacedClassI_row_spec
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K) :
    cglPrimitiveClassINaturalWellSpacedTailWitness X Y n χ τ H K r.1 := by
  classical
  exact (Finset.mem_filter.mp r.2).2

/-- Each finite natural-spacing Class-II row has the exact finite
left-critical-line Mellin-integral witness. -/
theorem cglPrimitiveClassINaturalWellSpacedClassII_row_leftLine
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassINaturalWellSpacedClassIIRow X Y n χ τ H K) :
    cglPrimitiveClassINaturalWellSpacedLeftLineWitness X Y n χ τ H K r.1 := by
  classical
  rcases cglPrimitiveClassINaturalWellSpaced_tail_or_leftLine X Y n χ τ H K r.1 with htail | hleft
  · exact False.elim ((Finset.mem_filter.mp r.2).2 htail)
  · exact hleft

/-- The natural-spacing Class-I and Class-II subpackets partition their
explicit finite primitive zero-row carrier. -/
theorem cglPrimitiveClassINaturalWellSpacedClass_rows_card
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :
    (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card +
      (cglPrimitiveClassINaturalWellSpacedClassIIRows X Y n χ τ H K).card =
        (cglPrimitiveClassINaturalWellSpacedAllRows n χ τ H K).card := by
  classical
  simpa only [cglPrimitiveClassINaturalWellSpacedClassIRows,
    cglPrimitiveClassINaturalWellSpacedClassIIRows] using
    (Finset.card_filter_add_card_filter_not
      (s := (cglPrimitiveClassINaturalWellSpacedAllRows n χ τ H K))
      (cglPrimitiveClassINaturalWellSpacedTailWitness X Y n χ τ H K))

end RHTower
