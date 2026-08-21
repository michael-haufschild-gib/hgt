/-
# Chen--Gupta--Li primitive Class-II maximizer rows

Each finite primitive row in the left-critical-line branch carries a canonical
truncation depth.  This module uses it to select the source-style local
critical-line L-value maximizer and records the exact CGL character/ordinate
row needed by the later fourth-moment step.

No RH, GRH, zero-density, zero-detection, large-value, or moment premise is
supplied by callers.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveZeroPartition
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILocalMaximizer

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-- Canonical finite left-critical-line truncation depth carried by a selected
Class-II row. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIILeftLineDepth
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) : ℕ :=
  Classical.choose (cglPrimitiveClassIWellSpacedClassII_row_leftLine X Y n χ τ H r)

/-- The chosen left-line truncation retains the exact finite critical-line
integral lower bound. -/
theorem cglPrimitiveClassIWellSpacedClassIILeftLineDepth_large
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
      ‖(1 / (2 * Real.pi) : ℝ) •
        (∫ t in
          (-((cglPrimitiveClassIWellSpacedClassIILeftLineDepth X Y n χ τ H r + 1 : ℕ) : ℝ))..
            ((cglPrimitiveClassIWellSpacedClassIILeftLineDepth X Y n χ τ H r + 1 : ℕ) : ℝ),
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H
              (cglPrimitiveClassIWellSpacedZero n χ τ H r.1)).toCGLNonprincipalCriticalStripLZero
            ((((1 / 2 : ℝ) -
              (cglPrimitiveClassIWellSpacedZero n χ τ H r.1).1.1.re : ℝ) : ℂ) +
                (t : ℂ) * I))‖ := by
  exact Classical.choose_spec
    (cglPrimitiveClassIWellSpacedClassII_row_leftLine X Y n χ τ H r)

/-- Radius of the local critical-line maximum window attached to a selected
Class-II row. -/
def cglPrimitiveClassIWellSpacedClassIIMaximizerRadius
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) : NNReal :=
  ⟨(cglPrimitiveClassIWellSpacedClassIILeftLineDepth X Y n χ τ H r + 1 : ℕ), by positivity⟩

/-- The actual CGL character/ordinate row at the local critical-line L-value
maximum associated to a selected Class-II zero row. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIIMaximizerRow
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    CGLCharacterDyadicRowData (n + 1) :=
  cglClassIICriticalLineLocalMaximizerRow n χ.1.1
    (cglPrimitiveClassIWellSpacedZero n χ τ H r.1).1.1.im
    (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r)

/-- The local-maximizer row retains its original primitive character. -/
theorem cglPrimitiveClassIWellSpacedClassIIMaximizerRow_character
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    (cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).character = χ.1.1 := by
  exact cglClassIICriticalLineLocalMaximizerRow_character n χ.1.1
    (cglPrimitiveClassIWellSpacedZero n χ τ H r.1).1.1.im
    (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r)

/-- The selected maximum remains inside the literal local interval around its
source zero ordinate. -/
theorem cglPrimitiveClassIWellSpacedClassIIMaximizerRow_time_displacement_le
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    |(cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).time -
      (cglPrimitiveClassIWellSpacedZero n χ τ H r.1).1.1.im| ≤
        cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r := by
  exact cglClassIICriticalLineLocalMaximizerRow_time_displacement_le n χ.1.1
    (cglPrimitiveClassIWellSpacedZero n χ τ H r.1).1.1.im
    (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r)

end RHTower
