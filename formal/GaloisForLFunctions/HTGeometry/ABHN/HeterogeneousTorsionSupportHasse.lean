import GaloisForLFunctions.HTGeometry.ABHN.HeterogeneousTorsionReciprocity
import GaloisForLFunctions.HTGeometry.ABHN.ReciprocitySupportCardinality

/-!
# Support rigidity for heterogeneous torsion reciprocity

Place-dependent finite torsion coordinates embed faithfully in the common `ℚ/ℤ` invariant
group. Therefore a nonzero heterogeneous profile in the reciprocity kernel cannot be supported at
one place, even when local torsion orders and carrier groups vary with the place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

/-- Inclusion of a place-dependent finite torsion coordinate in `ℚ/ℤ` is injective. -/
theorem heterogeneousTorsionLocalInvariantAddHom_injective
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) (i : ι) :
    Function.Injective (heterogeneousTorsionLocalInvariantAddHom A n e i) := by
  intro x y hxy
  apply (e i).injective
  apply Subtype.ext
  exact hxy

/-- A nonzero heterogeneous torsion profile with zero invariant sum occupies at least two
places. -/
theorem heterogeneousTorsionProfile_two_le_support_card_of_sum_eq_zero
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i))
    (f : Π₀ i, A i)
    (hf : heterogeneousTorsionProfileInvariantSumAddHom A n e f = 0)
    (hne : f ≠ 0) :
    2 ≤ f.support.card := by
  apply heterogeneousRatModIntProfile_two_le_support_card_of_mem_kernel
    A (heterogeneousTorsionLocalInvariantAddHom A n e)
    (fun i => heterogeneousTorsionLocalInvariantAddHom_injective A n e i) f
  · exact hf
  · exact hne

/-- A nonzero heterogeneous torsion profile with zero invariant sum has two distinct nonzero
local coordinates. -/
theorem heterogeneousTorsionProfile_exists_two_nonzero_places_of_sum_eq_zero
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i))
    (f : Π₀ i, A i)
    (hf : heterogeneousTorsionProfileInvariantSumAddHom A n e f = 0)
    (hne : f ≠ 0) :
    ∃ i j, i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 := by
  apply heterogeneousRatModIntProfile_exists_two_nonzero_places_of_mem_kernel
    A (heterogeneousTorsionLocalInvariantAddHom A n e)
    (fun i => heterogeneousTorsionLocalInvariantAddHom_injective A n e i) f
  · exact hf
  · exact hne

/-- Every specified nonzero coordinate of a zero-sum heterogeneous torsion profile has a
distinct nonzero partner. -/
theorem heterogeneousTorsionProfile_exists_other_nonzero_place_of_sum_eq_zero
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i))
    (f : Π₀ i, A i)
    (hf : heterogeneousTorsionProfileInvariantSumAddHom A n e f = 0)
    {i : ι} (hi : f i ≠ 0) :
    ∃ j, j ≠ i ∧ f j ≠ 0 := by
  apply heterogeneousRatModIntProfile_exists_other_nonzero_place_of_mem_kernel
    A (heterogeneousTorsionLocalInvariantAddHom A n e)
    (fun j => heterogeneousTorsionLocalInvariantAddHom_injective A n e j) f
  · exact hf
  · exact hi

end


end GaloisForLFunctions.HTGeometry.ABHN
