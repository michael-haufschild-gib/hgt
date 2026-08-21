/-
# Chen--Gupta--Li primitive Class-I common-prefix fibers

Partitions the finite Class-I packet into exact fibers with common dyadic
length and natural prefix cutoff.  Each anchored fiber has a positive common
threshold attained by the same bounded common-coefficient polynomial at every
member row.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassICommonPrefixCutoff

open Complex

noncomputable section

namespace RHTower

/-- Discrete key identifying the common coefficient vector of a Class-I prefix. -/
def cglPrimitiveClassIWellSpacedClassIPacketPrefixKey
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) : ℕ × ℕ :=
  (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i,
    cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i))

/-- The finite fiber of packet rows sharing an anchor's dyadic length and cutoff. -/
def cglPrimitiveClassIWellSpacedClassIPrefixFiber
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    Finset (Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :=
  Finset.univ.filter (fun j =>
    cglPrimitiveClassIWellSpacedClassIPacketPrefixKey X Y n χ τ H j =
      cglPrimitiveClassIWellSpacedClassIPacketPrefixKey X Y n χ τ H i)

/-- Every anchored prefix fiber contains its anchor. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiber_self_mem
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    i ∈ cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i := by
  simp [cglPrimitiveClassIWellSpacedClassIPrefixFiber]

/-- Fiber membership fixes the full discrete common-prefix key. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiber_key_eq
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i j : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (hj : j ∈ cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i) :
    cglPrimitiveClassIWellSpacedClassIPacketPrefixKey X Y n χ τ H j =
      cglPrimitiveClassIWellSpacedClassIPacketPrefixKey X Y n χ τ H i := by
  simpa [cglPrimitiveClassIWellSpacedClassIPrefixFiber] using hj

/-- Fiber membership fixes dyadic length. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiber_length_eq
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i j : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (hj : j ∈ cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i) :
    cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H j =
      cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i := by
  have hkey := cglPrimitiveClassIWellSpacedClassIPrefixFiber_key_eq X Y n χ τ H i j hj
  simpa [cglPrimitiveClassIWellSpacedClassIPacketPrefixKey] using congrArg Prod.fst hkey

/-- Fiber membership fixes natural cutoff. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiber_cutoff_eq
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i j : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (hj : j ∈ cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i) :
    cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H j) =
      cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i) := by
  have hkey := cglPrimitiveClassIWellSpacedClassIPrefixFiber_key_eq X Y n χ τ H i j hj
  simpa [cglPrimitiveClassIWellSpacedClassIPacketPrefixKey] using congrArg Prod.snd hkey

/-- Positive row-level prefix threshold stored as `NNReal`. -/
def cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) : NNReal :=
  (cglPrimitiveClassIWellSpacedClassIPrefixThreshold X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)).toNNReal

/-- Every stored row-level prefix threshold is strictly positive. -/
theorem cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    0 < cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold X Y n χ τ H i := by
  rw [cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold, Real.toNNReal_pos]
  exact cglPrimitiveClassIWellSpacedClassIPrefixThreshold_pos X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)

/-- Each stored threshold is attained by its row's natural-cutoff prefix polynomial. -/
theorem cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold_le_polynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    (cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold X Y n χ τ H i : ℝ) ≤
      ‖cglClassINatPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i) n
        (cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H
          (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)) χ.1.1
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H
          (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i))‖ := by
  have hnonneg : 0 ≤ cglPrimitiveClassIWellSpacedClassIPrefixThreshold X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i) :=
    (cglPrimitiveClassIWellSpacedClassIPrefixThreshold_pos X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)).le
  rw [show (cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold X Y n χ τ H i : ℝ) =
      cglPrimitiveClassIWellSpacedClassIPrefixThreshold X Y n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i) by
      exact Real.coe_toNNReal _ hnonneg]
  simpa [cglPrimitiveClassIWellSpacedClassIPacketTailLength] using
    cglPrimitiveClassIWellSpacedClassIPrefixThreshold_le_natPolynomial X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)

/-- Common positive threshold of an anchored nonempty Class-I prefix fiber. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) : NNReal :=
  Finset.inf' (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i)
    ⟨i, cglPrimitiveClassIWellSpacedClassIPrefixFiber_self_mem X Y n χ τ H i⟩
    (cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold X Y n χ τ H)

/-- Every anchored fiber's common threshold is strictly positive. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    0 < cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i := by
  unfold cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold
  apply (Finset.lt_inf'_iff ⟨i,
    cglPrimitiveClassIWellSpacedClassIPrefixFiber_self_mem X Y n χ τ H i⟩).mpr
  intro j hj
  exact cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold_pos X Y n χ τ H j

/-- Fiber threshold is no greater than each row-level threshold in that fiber. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold_le_rowThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i j : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (hj : j ∈ cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i) :
    cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i ≤
      cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold X Y n χ τ H j := by
  unfold cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold
  exact Finset.inf'_le _ hj

/-- Every member of a fiber exceeds that fiber's one common positive threshold
under the one common bounded coefficient vector. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold_le_commonPolynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i j : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (hj : j ∈ cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i) :
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i : ℝ) ≤
      ‖cglClassINatPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H i) n
        (cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H
          (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H i)) χ.1.1
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H
          (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H j))‖ := by
  calc
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold X Y n χ τ H i : ℝ) ≤
        (cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold X Y n χ τ H j : ℝ) := by
      exact_mod_cast cglPrimitiveClassIWellSpacedClassIPrefixFiberThreshold_le_rowThreshold
        X Y n χ τ H i j hj
    _ ≤ ‖cglClassINatPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassIWellSpacedClassIPacketTailLength X Y n χ τ H j) n
        (cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H
          (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H j)) χ.1.1
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H
          (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H j))‖ :=
      cglPrimitiveClassIWellSpacedClassIPacketPrefixThreshold_le_polynomial X Y n χ τ H j
    _ = _ := by
      rw [cglPrimitiveClassIWellSpacedClassIPrefixFiber_length_eq X Y n χ τ H i j hj,
        cglPrimitiveClassIWellSpacedClassIPrefixFiber_cutoff_eq X Y n χ τ H i j hj]

end RHTower
