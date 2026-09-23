import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanFiniteCuspOverlap

/-!
# Scale-relative finite overlap at number-field cusps

The full positive cone contains every positive scalar multiple of a form, and the special-linear
action preserves that scale.  Consequently fixed absolute coercivity and diagonal bounds cannot
describe a covering cusp family.  The correct overlap argument uses a positive, action-invariant
placewise scale.  Source coercivity and target diagonal bounds both contain that scale, which
cancels before Minkowski discreteness is applied.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Coercivity relative to a positive placewise scale. -/
def NumberFieldArchimedeanIsRelativelyCoercive
    (scale : numberFieldArchimedeanPositiveForms K n → InfinitePlace K → ℝ)
    (c : ℝ) (A : numberFieldArchimedeanPositiveForms K n) : Prop :=
  (∀ (w : {w : InfinitePlace K // w.IsReal}) (v : Fin n → ℝ),
      (c * scale A w.1) * ∑ k, (v k) ^ (2 : ℕ) ≤
        v ⬝ᵥ ((A.1.1 w : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)) ∧
    ∀ (w : {w : InfinitePlace K // w.IsComplex}) (v : Fin n → ℂ),
      (c * scale A w.1) * ∑ k, ‖v k‖ ^ (2 : ℕ) ≤
        (star v ⬝ᵥ ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)).re

/-- Diagonal boundedness relative to the same placewise scale. -/
def NumberFieldArchimedeanIsRelativelyDiagonallyBounded
    (scale : numberFieldArchimedeanPositiveForms K n → InfinitePlace K → ℝ)
    (C : ℝ) (A : numberFieldArchimedeanPositiveForms K n) : Prop :=
  (∀ (w : {w : InfinitePlace K // w.IsReal}) (i : Fin n),
      (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) i i ≤ C * scale A w.1) ∧
    ∀ (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin n),
      ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) i i).re ≤ C * scale A w.1

/-- **Scale-relative finite overlap.**  Transitions between relatively coercive and relatively
diagonally bounded cusp families are finite whenever the positive scale is invariant under the
integral special-linear action. -/
theorem finite_numberFieldArchimedean_relativeTransitionSet
    (scale : numberFieldArchimedeanPositiveForms K n → InfinitePlace K → ℝ)
    (c C : ℝ) (hc : 0 < c)
    (hscalePos : ∀ A w, 0 < scale A w)
    (hscaleInv : ∀ (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) A w,
      scale (g • A) w = scale A w)
    (V W : Set (numberFieldArchimedeanPositiveForms K n))
    (hV : ∀ A ∈ V, NumberFieldArchimedeanIsRelativelyCoercive scale c A)
    (hW : ∀ A ∈ W, NumberFieldArchimedeanIsRelativelyDiagonallyBounded scale C A) :
    {g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) |
      ∃ A ∈ V, g • A ∈ W}.Finite := by
  let R := Real.sqrt (C / c)
  let T : Set (Matrix (Fin n) (Fin n) (𝓞 K)) :=
    {N |
      (∀ i j, ∀ w : {w : InfinitePlace K // w.IsReal},
        |InfinitePlace.embedding_of_isReal w.prop (N i j : K)| ≤ R) ∧
      (∀ i j, ∀ w : {w : InfinitePlace K // w.IsComplex},
        ‖w.val.embedding (N i j : K)‖ ≤ R)}
  have hT : T.Finite :=
    finite_numberFieldIntegerMatrix_of_archimedean_bound n R (Real.sqrt_nonneg _)
  refine (hT.preimage (f := fun g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) =>
    (g : Matrix (Fin n) (Fin n) (𝓞 K))) ?_).subset ?_
  · intro g _ h _ hgh
    exact Subtype.ext hgh
  · rintro g ⟨A, hAV, hgAW⟩
    have hcoercive := hV A hAV
    have hbounded := hW (g • A) hgAW
    constructor
    · intro i j w
      let s := scale A w.1
      have hs : 0 < s := hscalePos A w.1
      have hdiag : ∀ k,
          ((g • A).1.1 w : Matrix (Fin n) (Fin n) ℝ) k k ≤ C * s := by
        intro k
        simpa [s, hscaleInv g A w.1] using hbounded.1 w k
      have hb := real_congruence_entry_bound (mul_pos hc hs)
        (hcoercive.1 w) hdiag
        (show ((g • A).1.1 w : Matrix (Fin n) (Fin n) ℝ) =
            numberFieldRealOrderMatrixAt w
                (g : Matrix (Fin n) (Fin n) (𝓞 K)) *
              (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) *
              (numberFieldRealOrderMatrixAt w
                (g : Matrix (Fin n) (Fin n) (𝓞 K)))ᵀ by rfl) i j
      have hratio : (C * s) / (c * s) = C / c := by
        field_simp
      rw [hratio] at hb
      simpa [R, numberFieldRealOrderMatrixAt] using hb
    · intro i j w
      let s := scale A w.1
      have hs : 0 < s := hscalePos A w.1
      have hdiag : ∀ k,
          (((g • A).1.2 w : Matrix (Fin n) (Fin n) ℂ) k k).re ≤ C * s := by
        intro k
        simpa [s, hscaleInv g A w.1] using hbounded.2 w k
      have hb := complex_congruence_entry_bound (mul_pos hc hs)
        (hcoercive.2 w) hdiag
        (show ((g • A).1.2 w : Matrix (Fin n) (Fin n) ℂ) =
            numberFieldComplexOrderMatrixAt w
                (g : Matrix (Fin n) (Fin n) (𝓞 K)) *
              (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) *
              (numberFieldComplexOrderMatrixAt w
                (g : Matrix (Fin n) (Fin n) (𝓞 K)))ᴴ by rfl) i j
      have hratio : (C * s) / (c * s) = C / c := by
        field_simp
      rw [hratio] at hb
      simpa [R, numberFieldComplexOrderMatrixAt] using hb

end

end GaloisForLFunctions.HTGeometry
