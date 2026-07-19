import GaloisForLFunctions.HTGeometry.MixedChamberMargin

/-!
# The negative coordinate subspace has dimension the chamber grading

The vectors supported in the negative coordinates are exactly the tuples indexed by those
coordinates, so the subspace is linearly isomorphic to a coordinate space of that size and its
dimension is the number of negative coefficients.

That number is the chamber grading, so the negative-definite subspace produced by the mixed-chamber
margin has exactly the dimension the lower bound requires.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

open scoped Classical

/-- **The negative coordinate subspace is a coordinate space.** -/
def negSupportedEquiv {d : ℕ} (c : Fin d → ℝ) :
    negSupported c ≃ₗ[ℂ] ({j : Fin d // c j < 0} → ℂ) where
  toFun x := fun j => (x : Fin d → ℂ) j.1
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl
  invFun f := ⟨fun i => if h : c i < 0 then f ⟨i, h⟩ else 0, by
    intro j hj
    simp [hj]⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    by_cases h : c i < 0
    · simp [h]
    · simp only [h, dif_neg, not_false_iff]
      exact ((mem_negSupported c _).1 x.2 i h).symm
  right_inv := by
    intro f
    funext j
    simp [j.2]

/-- **The chamber grading is the dimension of the negative coordinate subspace.** -/
theorem finrank_negSupported {d : ℕ} (c : Fin d → ℝ) :
    Module.finrank ℂ (negSupported c) = negCount c := by
  classical
  rw [(negSupportedEquiv c).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype]
  rfl

end

end GaloisForLFunctions.HTGeometry
