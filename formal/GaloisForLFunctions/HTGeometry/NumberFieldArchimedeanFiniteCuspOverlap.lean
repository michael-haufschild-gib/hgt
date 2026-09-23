import GaloisForLFunctions.HTGeometry.FiniteCuspMacbeath
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBoundedOverlap

/-!
# Finite overlap between number-field cusp families

A uniformly coercive source form and a diagonally bounded target form bound every entry of an
integral congruence matrix at every infinite place.  Minkowski discreteness then leaves finitely
many number-ring matrices.  This module packages that argument directly as pairwise finiteness of
transition sets between cusp neighbourhoods, the input expected by `FiniteCuspMacbeath`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Uniform placewise coercivity for a family of number-field archimedean forms. -/
def NumberFieldArchimedeanIsUniformlyCoercive (c : ℝ)
    (A : numberFieldArchimedeanPositiveForms K n) : Prop :=
  (∀ (w : {w : InfinitePlace K // w.IsReal}) (v : Fin n → ℝ),
      c * ∑ k, (v k) ^ (2 : ℕ) ≤
        v ⬝ᵥ ((A.1.1 w : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)) ∧
    ∀ (w : {w : InfinitePlace K // w.IsComplex}) (v : Fin n → ℂ),
      c * ∑ k, ‖v k‖ ^ (2 : ℕ) ≤
        (star v ⬝ᵥ ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)).re

/-- Uniform placewise diagonal upper bound for a family of number-field archimedean forms. -/
def NumberFieldArchimedeanIsDiagonallyBounded (C : ℝ)
    (A : numberFieldArchimedeanPositiveForms K n) : Prop :=
  (∀ (w : {w : InfinitePlace K // w.IsReal}) (i : Fin n),
      (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) i i ≤ C) ∧
    ∀ (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin n),
      ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) i i).re ≤ C

/-- Transitions from a uniformly coercive family to a uniformly diagonally bounded family form a
finite subset of the number-ring special linear group. -/
theorem finite_numberFieldArchimedean_transitionSet
    (c C : ℝ) (hc : 0 < c)
    (V W : Set (numberFieldArchimedeanPositiveForms K n))
    (hV : ∀ A ∈ V, NumberFieldArchimedeanIsUniformlyCoercive c A)
    (hW : ∀ A ∈ W, NumberFieldArchimedeanIsDiagonallyBounded C A) :
    {g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) |
      ∃ A ∈ V, g • A ∈ W}.Finite := by
  let T : Set (Matrix (Fin n) (Fin n) (𝓞 K)) :=
    {N | NumberFieldRealCongruenceBound c C N ∧
      NumberFieldComplexCongruenceBound c C N}
  have hT : T.Finite :=
    finite_numberFieldIntegerMatrix_of_archimedean_congruenceBounds n c C hc
  refine (hT.preimage (f := fun g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) =>
    (g : Matrix (Fin n) (Fin n) (𝓞 K))) ?_).subset ?_
  · intro g _ h _ hgh
    exact Subtype.ext hgh
  · rintro g ⟨A, hAV, hgAW⟩
    have hcoercive := hV A hAV
    have hbounded := hW (g • A) hgAW
    constructor
    · intro w
      refine ⟨(A.1.1 w : Matrix (Fin n) (Fin n) ℝ),
        ((g • A).1.1 w : Matrix (Fin n) (Fin n) ℝ),
        hcoercive.1 w, hbounded.1 w, ?_⟩
      change _ = numberFieldRealOrderMatrixAt w
          (g : Matrix (Fin n) (Fin n) (𝓞 K)) *
        (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) *
          (numberFieldRealOrderMatrixAt w
            (g : Matrix (Fin n) (Fin n) (𝓞 K)))ᵀ
      rfl
    · intro w
      refine ⟨(A.1.2 w : Matrix (Fin n) (Fin n) ℂ),
        ((g • A).1.2 w : Matrix (Fin n) (Fin n) ℂ),
        hcoercive.2 w, hbounded.2 w, ?_⟩
      rfl

end

end GaloisForLFunctions.HTGeometry
