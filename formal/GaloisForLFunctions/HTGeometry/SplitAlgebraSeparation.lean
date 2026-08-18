import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Data.Fintype.Card

/-!
# A separating element of a split finite algebra

Over an infinite field, an algebra that surjects onto `K^n` through `n` algebra maps has an element
whose images under them are pairwise distinct.  Together with
`Matrix.det_vandermonde_ne_zero_iff` this is the existence half of the chart datum for the general
simple connectedness of the affine line: the powers of such an element form a basis of the fibre.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- **A separating element of a split finite algebra.**  If a `K`-algebra has `n` distinct
`K`-algebra maps to `K` and the corresponding map to `K^n` is surjective, some element separates
them. -/
theorem exists_separating_of_surjective {K C : Type*} [Field K] [Infinite K] [CommRing C]
    [Algebra K C] {n : ℕ} (χ : Fin n → C →ₐ[K] K)
    (hsurj : Function.Surjective fun c : C => fun i => χ i c) :
    ∃ θ : C, Function.Injective fun i => χ i θ := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Fin n → K, Function.Injective a := by
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq K n
    obtain ⟨f⟩ : Nonempty (Fin n ≃ (s : Set K)) := by
      refine ⟨(Fintype.equivFinOfCardEq ?_).symm⟩
      simpa using hs
    exact ⟨fun i => (f i : K), fun i j h => f.injective (Subtype.ext h)⟩
  obtain ⟨θ, hθ⟩ := hsurj a
  refine ⟨θ, ?_⟩
  intro i j hij
  apply ha
  have hi : χ i θ = a i := congrFun hθ i
  have hj : χ j θ = a j := congrFun hθ j
  rw [← hi, ← hj]
  exact hij

end GaloisForLFunctions.HTGeometry
