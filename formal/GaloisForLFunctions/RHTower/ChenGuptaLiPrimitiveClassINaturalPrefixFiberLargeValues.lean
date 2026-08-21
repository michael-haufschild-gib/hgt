/-
# Chen--Gupta--Li coarse Class-I common-prefix fiber large values

Instantiates the unconditional finite character large-value and energy
interfaces for every coarse common-prefix fiber.  Every reindexed fiber row is
proved to be a large value of that fiber's one bounded common coefficient
vector at its one certified positive threshold.

No RH, GRH, zero-density, large-value, or moment premise is supplied by a
caller.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalPrefixFiberMatrix

open Complex

noncomputable section

namespace RHTower

/-- Exact finite character large-value set of an anchored coarse fiber. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberLargeValues
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    Finset (Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card) :=
  cglCharacterDyadicLargeValues
    (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i) (n + 1)
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i)
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H K i)
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i)

theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_mem_largeValues
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (k : Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card) :
    k ∈ cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberLargeValues X Y n χ τ H K i := by
  unfold cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberLargeValues
    cglCharacterDyadicLargeValues
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold_le_matrixPolynomial
    X Y n χ τ H K i k

/-- Every reindexed coarse fiber row is a large value. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_largeValues_eq_univ
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberLargeValues X Y n χ τ H K i = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro k hk
  exact cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_mem_largeValues X Y n χ τ H K i k

/-- Unconditional finite character-energy bound for every coarse
common-prefix fiber. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_card_mul_threshold_sq_le
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    ((cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card : ℝ) *
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i : ℝ) ^ 2 ≤
      ((cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card : ℝ) *
        (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i : ℝ) *
          ‖cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H K i‖ ^ 2 := by
  have hbase := card_cglCharacterDyadicLargeValues_mul_sq_le
    (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i) (n + 1)
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i)
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H K i)
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i)
  change
    ((cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberLargeValues X Y n χ τ H K i).card : ℝ) *
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i : ℝ) ^ 2 ≤
      ((cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card : ℝ) *
        (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i : ℝ) *
          ‖cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberCoefficients X Y n χ τ H K i‖ ^ 2 at hbase
  rw [cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_largeValues_eq_univ] at hbase
  simpa using hbase

end RHTower
