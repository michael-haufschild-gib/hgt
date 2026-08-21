/-
# Chen--Gupta--Li coarse Class-I common-prefix fibers

Partitions the finite `(K + 1)`-spaced Class-I packet by the exact discrete
data determining its bounded common coefficient vector: dyadic length and
natural prefix cutoff.  This leaves every primitive zero and its certified
coarse ordinate spacing unchanged.

No RH, GRH, zero-density, large-value, or moment premise is supplied by a
caller.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalCommonPrefixWitness

noncomputable section

namespace RHTower

/-- Canonical enumeration of the finite coarse Class-I packet. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPacketIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n χ τ H K :=
  (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).equivFin.symm i

/-- Dyadic tail length attached to one enumerated coarse Class-I row. -/
def cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) : ℕ :=
  cglPrimitiveClassINaturalWellSpacedClassITailLength X Y n χ τ H K
    (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i)

/-- Discrete key of the literal bounded common coefficient vector. -/
def cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixKey
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) : ℕ × ℕ :=
  (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i,
    cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i))

/-- Finite fiber sharing its anchor's exact common coefficient vector. -/
def cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    Finset (Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :=
  Finset.univ.filter (fun j =>
    cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixKey X Y n χ τ H K j =
      cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixKey X Y n χ τ H K i)

/-- Each common-prefix fiber contains its anchor. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_self_mem
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    i ∈ cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i := by
  simp [cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber]

/-- Fiber membership fixes the complete common-prefix key. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_key_eq
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i j : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (hj : j ∈ cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i) :
    cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixKey X Y n χ τ H K j =
      cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixKey X Y n χ τ H K i := by
  simpa [cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber] using hj

/-- Fiber membership fixes the dyadic length. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_length_eq
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i j : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (hj : j ∈ cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i) :
    cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K j =
      cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i := by
  have hkey := cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_key_eq X Y n χ τ H K i j hj
  simpa [cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixKey] using congrArg Prod.fst hkey

/-- Fiber membership fixes the natural prefix cutoff. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_cutoff_eq
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i j : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (hj : j ∈ cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i) :
    cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K j) =
      cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff X Y n χ τ H K
        (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i) := by
  have hkey := cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_key_eq X Y n χ τ H K i j hj
  simpa [cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixKey] using congrArg Prod.snd hkey

end RHTower
