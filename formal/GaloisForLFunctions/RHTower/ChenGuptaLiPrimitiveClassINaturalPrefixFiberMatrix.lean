/-
# Chen--Gupta--Li coarse Class-I common-prefix fiber matrix

Reindexes each finite `(K + 1)`-spaced common-prefix fiber as the exact finite
Dirichlet-character/ordinate matrix used by the existing CGL large-value
infrastructure.  Its one coefficient vector and one threshold are literal
fiber data.

No RH, GRH, zero-density, large-value, or moment premise is supplied by a
caller.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalPrefixFiberThreshold

open Complex

noncomputable section

namespace RHTower

/-- Canonical finite enumeration of an anchored coarse common-prefix fiber. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (k : Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card) :
    Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card :=
  ((cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).equivFin.symm k).1

theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex_mem
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (k : Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card) :
    cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i k ∈
      cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i :=
  ((cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).equivFin.symm k).2

/-- Exact character/ordinate rows of the enumerated coarse fiber. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card →
      CGLCharacterDyadicRowData (n + 1) :=
  fun k => cglShiftedTailDyadicRow χ.1.1
    (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i k)))

/-- The one bounded common coefficient vector shared by an entire coarse fiber. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberCoefficients
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    EuclideanSpace ℂ (Fin (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i)) :=
  cglClassIPrefixScaledCoefficients X
    (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i)
    (cglClassIPrefixIndexOfNat
      (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i)
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff X Y n χ τ H K
        (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i)))

/-- The fiber threshold is attained by every row of its exact character matrix. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold_le_matrixPolynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (k : Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card) :
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i : ℝ) ≤
      ‖cglCharacterDyadicPolynomial
        (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i) (n + 1)
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i k)
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H K i)‖ := by
  have hmem := cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex_mem X Y n χ τ H K i k
  simpa [cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows,
    cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberCoefficients,
    cglClassINatPrefixScaledDetectorPolynomial,
    cglClassIPrefixScaledDetectorPolynomial] using
    cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold_le_commonPolynomial
      X Y n χ τ H K i
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i k) hmem

end RHTower
