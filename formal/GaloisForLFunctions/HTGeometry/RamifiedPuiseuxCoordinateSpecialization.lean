import GaloisForLFunctions.HTGeometry.RamifiedPuiseuxBranchField

/-!
# Coordinate-level construction of a ramified Puiseux specialization

A selected algebraic branch is normally specified on the state coordinates and their selected
velocities, not by postulating commutation on every element of the resulting algebraic function
field.  This module proves that coordinate agreement is enough.  Algebraicity of the source over
its coordinate field and characteristic-zero uniqueness of derivations force the complete
differential specialization required by the observability theorem.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

/-- **Coordinate branch data force the full ramified Puiseux specialization.**  The source field
is algebraic over the displayed coordinates.  If an embedding sends those coordinates to the
ramified Hahn coordinates, sends their time derivatives to the selected suffix products, and the
source coordinate frame is the matching negative Kronecker frame, then every source element—not
only the generators—intertwines both the time and coordinate derivations. -/
theorem isRamifiedPuiseuxCascadeSpecialization_of_coordinates {n : ℕ} {K : Type*}
    [Field K] [CharZero K] [Algebra ℂ K]
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (x : Fin (n + 1) → K)
    [Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range x)) K]
    (pi : K →ₐ[ℂ] HahnFraction (mgDeg (n + 1)) ℂ)
    (delta : Derivation ℂ K K) (P : Fin (n + 1) → Derivation ℂ K K)
    (hcoord : ∀ k, pi (x k) = hahnFractionRamCoordinate r k)
    (hlaw : ∀ k, pi (delta (x k)) = hahnFractionRamSuffixProduct A (k : ℕ))
    (hframe : ∀ j k, P j (x k) = algebraMap ℂ K (if k = j then -1 else 0)) :
    IsRamifiedPuiseuxCascadeSpecialization r A pi delta P (x 0) := by
  refine ⟨hcoord 0, ?_, ?_⟩
  · apply derivation_map_eq_of_isAlgebraic_adjoin x pi delta
      (hahnFractionRamCascadeDerivation r A)
    intro k
    rw [hcoord, hahnFractionRamCascadeDerivation_coordinate r hr]
    exact hlaw k
  · intro j
    apply derivation_map_eq_of_isAlgebraic_adjoin x pi (P j) (hahnFractionRamPartial r j)
    intro k
    rw [hframe, pi.commutes, hcoord, hahnFractionRamPartial_coordinate r hr]

end GaloisForLFunctions.HTGeometry
