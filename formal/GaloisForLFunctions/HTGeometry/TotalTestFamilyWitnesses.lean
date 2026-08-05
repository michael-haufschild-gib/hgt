import GaloisForLFunctions.HTGeometry.SourcePointedPolarizationOrderLaw

/-!
# Total test families exist

A test family is total when only the zero source is orthogonal to all of it.  The family of *all*
vectors is total, because a vector orthogonal to itself vanishes; so the polarization order law
applies with no further input.  Totality is inherited by every family whose range contains a total
one, which is the form the law consumes.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The family of all vectors is total.** -/
theorem isTotalTestFamily_id : IsTotalTestFamily (id : H → H) := by
  intro x hx
  have hself : inner ℂ x x = (0 : ℂ) := hx x
  rwa [inner_self_eq_zero] at hself

/-- Totality is inherited from a subfamily with the same range. -/
theorem IsTotalTestFamily.of_range_subset {I J : Type*} {test : I → H} {test' : J → H}
    (h : IsTotalTestFamily test) (hsub : Set.range test ⊆ Set.range test') :
    IsTotalTestFamily test' := by
  intro x hx
  refine h x fun i => ?_
  obtain ⟨j, hj⟩ := hsub (Set.mem_range_self i)
  rw [← hj]
  exact hx j

/-- Every family whose range is all of the space is total. -/
theorem isTotalTestFamily_of_surjective {I : Type*} {test : I → H}
    (hsurj : Function.Surjective test) : IsTotalTestFamily test :=
  isTotalTestFamily_id.of_range_subset (by
    rw [hsurj.range_eq]
    exact Set.subset_univ _)

end GaloisForLFunctions.HTGeometry
