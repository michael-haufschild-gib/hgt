/-
# Chen--Gupta--Li Class-I common-prefix natural cutoff

Removes dependent-index friction from the finite common-prefix carrier.  The
selected `Fin (N+1)` prefix is represented by its natural cutoff, while exact
equality to the certified prefix polynomial and strict threshold positivity
are retained.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassICommonPrefixWitness

open Complex

noncomputable section

namespace RHTower

/-- Certified prefix index associated to any natural cutoff. -/
def cglClassIPrefixIndexOfNat (N K : ℕ) : Fin (N + 1) :=
  ⟨min K N, Nat.lt_succ_iff.mpr (min_le_right _ _)⟩

/-- Bounded common-coefficient prefix polynomial indexed by a natural cutoff. -/
def cglClassINatPrefixScaledDetectorPolynomial (X N q K : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) : ℂ :=
  cglClassIPrefixScaledDetectorPolynomial X N q (cglClassIPrefixIndexOfNat N K) χ s

/-- A natural cutoff from a certified index preserves the exact prefix polynomial. -/
theorem cglClassINatPrefixScaledDetectorPolynomial_of_fin (X N q : ℕ)
    (K : Fin (N + 1)) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) :
    cglClassINatPrefixScaledDetectorPolynomial X N q K.1 χ s =
      cglClassIPrefixScaledDetectorPolynomial X N q K χ s := by
  unfold cglClassINatPrefixScaledDetectorPolynomial cglClassIPrefixIndexOfNat
  have hK : K.1 ≤ N := Nat.lt_succ_iff.mp K.2
  simp only [Nat.min_eq_left hK]

/-- Natural cutoff of a row's canonical common-prefix witness. -/
def cglPrimitiveClassIWellSpacedClassIPrefixCutoff
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) : ℕ :=
  (cglPrimitiveClassIWellSpacedClassIPrefixIndex X Y n χ τ H r).1

/-- The per-row prefix threshold is attained by its natural-cutoff common
coefficient polynomial. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixThreshold_le_natPolynomial
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    cglPrimitiveClassIWellSpacedClassIPrefixThreshold X Y n χ τ H r ≤
      ‖cglClassINatPrefixScaledDetectorPolynomial X
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) n
        (cglPrimitiveClassIWellSpacedClassIPrefixCutoff X Y n χ τ H r) χ.1.1
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)‖ := by
  simpa [cglPrimitiveClassIWellSpacedClassIPrefixCutoff,
    cglClassINatPrefixScaledDetectorPolynomial_of_fin] using
    cglPrimitiveClassIWellSpacedClassIPrefixThreshold_le_polynomial X Y n χ τ H r

/-- Every per-row bounded common-prefix threshold is strictly positive. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixThreshold_pos
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIRow X Y n χ τ H) :
    0 < cglPrimitiveClassIWellSpacedClassIPrefixThreshold X Y n χ τ H r := by
  have hfull : 0 < cglClassIDyadicCoefficientScale X
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r) := by
    unfold cglClassIDyadicCoefficientScale
    positivity
  have htail : 0 < cglPrimitiveClassIWellSpacedClassITailThreshold X Y n χ τ H r := by
    unfold cglPrimitiveClassIWellSpacedClassITailThreshold
    have hdepth := cglPrimitiveClassIWellSpacedClassITailDepth_pos X Y n χ τ H r
    have hscale : 0 < cglShiftedTailDyadicCoefficientScale X
        (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
        (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ := by
      unfold cglShiftedTailDyadicCoefficientScale
      positivity
    positivity
  have hshift : 0 < cglShiftedTailDyadicCoefficientScale X
      (cglPrimitiveClassIWellSpacedClassITailLength X Y n χ τ H r)
      (cglPrimitiveClassIWellSpacedClassITailPoint n χ τ H r)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ := by
    unfold cglShiftedTailDyadicCoefficientScale
    positivity
  have hweight := cglPrimitiveClassIWellSpacedClassIInitialWeight_pos X Y n χ τ H r
  unfold cglPrimitiveClassIWellSpacedClassIPrefixThreshold
  exact div_pos (mul_pos hfull htail) (mul_pos hshift hweight)

end RHTower
