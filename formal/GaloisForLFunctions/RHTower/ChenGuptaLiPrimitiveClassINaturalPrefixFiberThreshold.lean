/-
# Chen--Gupta--Li coarse Class-I common-prefix fiber thresholds

Each finite coarse common-prefix fiber receives the minimum of its literal
positive row thresholds.  This proves one positive lower bound for one bounded
common coefficient vector at every fiber member, preserving the certified
`(K + 1)`-spaced primitive-zero carrier.

No RH, GRH, zero-density, large-value, or moment premise is supplied by a
caller.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalPrefixFibers

open Complex

noncomputable section

namespace RHTower

/-- Positive row threshold stored as nonnegative real data. -/
def cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) : NNReal :=
  (cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold X Y n χ τ H K
    (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i)).toNNReal

theorem cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    0 < cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold X Y n χ τ H K i := by
  rw [cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold, Real.toNNReal_pos]
  exact cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold_pos X Y n χ τ H K
    (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i)

theorem cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold_le_polynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    (cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold X Y n χ τ H K i : ℝ) ≤
      ‖cglClassINatPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i) n
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff X Y n χ τ H K
          (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i)) χ.1.1
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K
          (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i))‖ := by
  have hnonneg : 0 ≤ cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i) :=
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold_pos X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i)).le
  rw [show (cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold X Y n χ τ H K i : ℝ) =
      cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold X Y n χ τ H K
        (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i) by
      exact Real.coe_toNNReal _ hnonneg]
  simpa [cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength] using
    cglPrimitiveClassINaturalWellSpacedClassIPrefixThreshold_le_natPolynomial X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i)

/-- Positive common threshold of an anchored coarse common-prefix fiber. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) : NNReal :=
  Finset.inf' (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i)
    ⟨i, cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_self_mem X Y n χ τ H K i⟩
    (cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold X Y n χ τ H K)

theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    0 < cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i := by
  unfold cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold
  apply (Finset.lt_inf'_iff ⟨i,
    cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_self_mem X Y n χ τ H K i⟩).mpr
  intro j hj
  exact cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold_pos X Y n χ τ H K j

/-- Every coarse fiber member exceeds its anchor's single threshold under its
anchor's single bounded common coefficient vector. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold_le_commonPolynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i j : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (hj : j ∈ cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i) :
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i : ℝ) ≤
      ‖cglClassINatPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K i) n
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff X Y n χ τ H K
          (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K i)) χ.1.1
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K
          (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K j))‖ := by
  have hrow : cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i ≤
      cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold X Y n χ τ H K j := by
    unfold cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold
    exact Finset.inf'_le _ hj
  calc
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberThreshold X Y n χ τ H K i : ℝ) ≤
        (cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold X Y n χ τ H K j : ℝ) := by
      exact_mod_cast hrow
    _ ≤ ‖cglClassINatPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassINaturalWellSpacedClassIPacketTailLength X Y n χ τ H K j) n
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixCutoff X Y n χ τ H K
          (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K j)) χ.1.1
        (cglPrimitiveClassINaturalWellSpacedClassITailPoint n χ τ H K
          (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K j))‖ :=
      cglPrimitiveClassINaturalWellSpacedClassIPacketPrefixThreshold_le_polynomial X Y n χ τ H K j
    _ = _ := by
      rw [cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_length_eq X Y n χ τ H K i j hj,
        cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_cutoff_eq X Y n χ τ H K i j hj]

end RHTower
