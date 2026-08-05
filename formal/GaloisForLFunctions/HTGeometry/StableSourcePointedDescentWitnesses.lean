import GaloisForLFunctions.HTGeometry.SourcePointedExactDescentLaw

/-!
# Stable source-pointed exact descents exist

The stable descent interface is a conservativity, an exactness identity and a uniform lower bound
at once.  The identity observation with the zero compatibility realizes all three on the total
sector: the identity has trivial kernel, its image of everything is everything, and it is
isometric, so the recovery constant is one.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The identity observation is a stable source-pointed exact descent on the total sector.** -/
theorem isStableSourcePointedExactDescent_id {K E G : Type*} [NormedField K]
    [NormedAddCommGroup E] [NormedSpace K E] [AddCommGroup G] [Module K G] :
    IsStableSourcePointedExactDescent (LinearMap.id : E →ₗ[K] E) (0 : E →ₗ[K] G) ⊤ ⊤ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [IsConservativeOn, LinearMap.ker_id]
    exact disjoint_bot_right
  · rw [Submodule.map_id, LinearMap.ker_zero]
    simp
  · refine ⟨1, one_pos, fun x _ => ?_⟩
    rw [one_mul]
    exact le_of_eq rfl

end GaloisForLFunctions.HTGeometry
