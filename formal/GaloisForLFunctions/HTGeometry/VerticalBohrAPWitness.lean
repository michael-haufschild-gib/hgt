import GaloisForLFunctions.HTGeometry.VerticalStripBohrHull

/-!
# Bohr almost periodicity: attained, and reformulated

The uniform-return theorem consumes Bochner's criterion — relative compactness of the vertical
translation orbit — and nothing produced it.  It is attained by every function invariant under
vertical translation, in particular by every constant, so the criterion is not an empty condition
and the return theorem has instances.

Since bounded continuous functions form a complete metric space, the criterion is equivalent to
total boundedness of the orbit, which is the form in which it is usually verified.
-/

open BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

variable {S : Set ℂ}

/-- A function unchanged by every vertical translation satisfies Bochner's criterion: its orbit is
a single point. -/
theorem isVerticalBohrAP_of_translationInvariant (hS : IsVerticallyInvariant S) {g : S →ᵇ ℂ}
    (hinv : ∀ t : ℝ, bcfVerticalTranslate hS t g = g) :
    IsVerticalBohrAP hS g := by
  have hrange : (Set.range fun t : ℝ => bcfVerticalTranslate hS t g) = {g} := by
    rw [show (fun t : ℝ => bcfVerticalTranslate hS t g) = fun _ : ℝ => g from funext hinv]
    exact Set.range_const
  rw [IsVerticalBohrAP, hrange, closure_singleton]
  exact isCompact_singleton

/-- Constants are vertically almost periodic. -/
theorem isVerticalBohrAP_const (hS : IsVerticallyInvariant S) (c : ℂ) :
    IsVerticalBohrAP hS (BoundedContinuousFunction.const S c) := by
  refine isVerticalBohrAP_of_translationInvariant hS fun t => ?_
  ext z
  simp

/-- **Bochner's criterion is total boundedness of the orbit.**  Bounded continuous functions form a
complete metric space, so relative compactness of the vertical translation orbit is exactly its
total boundedness. -/
theorem isVerticalBohrAP_iff_totallyBounded (hS : IsVerticallyInvariant S) (g : S →ᵇ ℂ) :
    IsVerticalBohrAP hS g ↔
      TotallyBounded (Set.range fun t : ℝ => bcfVerticalTranslate hS t g) := by
  constructor
  · intro h
    exact h.totallyBounded.subset subset_closure
  · intro h
    exact TotallyBounded.isCompact_of_isClosed (TotallyBounded.closure h) isClosed_closure

end GaloisForLFunctions.HTGeometry
