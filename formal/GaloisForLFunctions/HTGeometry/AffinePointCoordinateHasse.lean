import GaloisForLFunctions.HTGeometry.AffineCoactionStabilizer

/-!
# Coordinate Hasse principle for affine points

A `C`-valued affine point is determined by all coordinate evaluations.  The full coordinate
profile is faithful, gives an equivalence with its realized range, and one coordinate detects every
pair of distinct points.

This is dual to point-evaluation reconstruction of coordinate-ring elements: here global functions
act as local probes that reconstruct the point itself.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable (C : Type u) (A : Type v) [CommRing C] [CommRing A] [Algebra C A]

/-- Complete coordinate-evaluation profile of a `C`-valued affine point. -/
def affinePointEvaluationProfile :
    (A →ₐ[C] C) → (A → C) :=
  fun p a ↦ p a

/-- All affine coordinates faithfully encode a `C`-valued point. -/
theorem affinePointEvaluationProfile_injective :
    Function.Injective (affinePointEvaluationProfile C A) := by
  intro p q h
  apply AlgHom.ext
  exact congrFun h

/-- Affine points are equivalent to the complete coordinate profiles they realize. -/
noncomputable def affinePointEvaluationProfileEquivRange :
    (A →ₐ[C] C) ≃ Set.range (affinePointEvaluationProfile C A) :=
  Equiv.ofInjective (affinePointEvaluationProfile C A)
    (affinePointEvaluationProfile_injective C A)

/-- Affine-coordinate Hasse congruence for `C`-valued points. -/
theorem affinePoint_congr_coordinate_hasse_iff (p q : A →ₐ[C] C) :
    p = q ↔ ∀ a : A, p a = q a := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    exact affinePointEvaluationProfile_injective C A (funext h)

/-- Distinct affine points are detected by one global coordinate. -/
theorem exists_affineCoordinate_ne_of_affinePoint_ne
    (p q : A →ₐ[C] C) (hpq : p ≠ q) :
    ∃ a : A, p a ≠ q a :=
  affineCoordinate_separates_points hpq

end

end GaloisForLFunctions.HTGeometry
