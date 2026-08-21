/-
# Chen--Gupta--Li Class-I common-prefix fiber large values

Reindexes each exact common-prefix fiber into the finite character matrix.
Every fiber member is proved to lie in the associated large-value set, and
the pre-existing unconditional character-energy inequality is instantiated
for that common bounded coefficient vector.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassICommonPrefixPacket

open Complex

noncomputable section

namespace RHTower

/-- Canonical finite enumeration of the rows in a common-prefix fiber. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (k : Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card) :
    Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card :=
  ((cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).equivFin.symm k).1

/-- Every enumerated fiber index belongs to its source fiber. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex_mem
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (k : Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card) :
    cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k ∈
      cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i :=
  ((cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).equivFin.symm k).2

/-- Character/ordinate rows of an enumerated common-prefix fiber. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIPrefixFiberRows
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card →
      CGLCharacterDyadicRowData (n + 1) :=
  fun k => cglShiftedTailDyadicRow χ.1.1
    (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k)))

/-- The one bounded coefficient vector shared by an entire common-prefix fiber. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficients
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    EuclideanSpace ℂ (Fin (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i)) :=
  cglClassIPrefixScaledCoefficients X
    (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i)
    (cglClassIPrefixIndexOfNat
      (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i)
      (cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)))

/-- The exact finite character large-value set for an anchored common-prefix fiber. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIPrefixFiberLargeValues
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    Finset (Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card) :=
  cglCharacterDyadicLargeValues
    (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i) (n + 1)
    (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i)
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H i)
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i)

/-- The fiber's shared threshold is attained by every enumerated matrix row. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold_le_matrixPolynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (k : Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card) :
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i : ℝ) ≤
      ‖cglCharacterDyadicPolynomial
        (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i) (n + 1)
        (cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i k)
        (cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H i)‖ := by
  have hmem := cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex_mem X Y n χ τ H i k
  simpa [cglPrimitiveClassIWellSpacedClassIPrefixFiberRows,
    cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficients,
    cglClassINatPrefixScaledDetectorPolynomial,
    cglClassIPrefixScaledDetectorPolynomial] using
    cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold_le_commonPolynomial
      X Y n χ τ H i
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k) hmem

/-- Every reindexed fiber row lies in its exact common-coefficient large-value set. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiber_mem_largeValues
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (k : Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card) :
    k ∈ cglPrimitiveClassIWellSpacedClassIPrefixFiberLargeValues X Y n χ τ H i := by
  unfold cglPrimitiveClassIWellSpacedClassIPrefixFiberLargeValues
    cglCharacterDyadicLargeValues
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold_le_matrixPolynomial X Y n χ τ H i k

/-- The fiber large-value set contains every index, hence is all of `Fin card`. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiber_largeValues_eq_univ
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    cglPrimitiveClassIWellSpacedClassIPrefixFiberLargeValues X Y n χ τ H i = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro k hk
  exact cglPrimitiveClassIWellSpacedClassIPrefixFiber_mem_largeValues X Y n χ τ H i k

/-- The shared common-prefix fiber coefficients satisfy the required coordinate bound. -/
theorem norm_cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficient_le_one
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (j : Fin (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i)) :
    ‖(cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H i) j‖ ≤ 1 := by
  exact norm_cglClassIPrefixScaledCoefficient_le_one X
    (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i)
    (cglClassIPrefixIndexOfNat
      (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i)
      (cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i))) j

/-- Unconditional finite character-energy bound for every common-prefix fiber. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiber_card_mul_threshold_sq_le
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    ((cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card : ℝ) *
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i : ℝ) ^ 2 ≤
      ((cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card : ℝ) *
        (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i : ℝ) *
          ‖cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H i‖ ^ 2 := by
  have hbase := card_cglCharacterDyadicLargeValues_mul_sq_le
    (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i) (n + 1)
    (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i)
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H i)
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i)
  change
    ((cglPrimitiveClassIWellSpacedClassIPrefixFiberLargeValues X Y n χ τ H i).card : ℝ) *
        (cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i : ℝ) ^ 2 ≤
      ((cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card : ℝ) *
        (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i : ℝ) *
          ‖cglPrimitiveClassIWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H i‖ ^ 2 at hbase
  rw [cglPrimitiveClassIWellSpacedClassIPrefixFiber_largeValues_eq_univ] at hbase
  simpa using hbase

end RHTower
