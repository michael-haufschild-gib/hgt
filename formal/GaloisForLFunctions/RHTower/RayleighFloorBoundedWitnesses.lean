import GaloisForLFunctions.RHTower.CCMNestedFloorNoEvacuation

/-!
# Rayleigh quotient sets bounded below

The nested-floor laws assume that the Rayleigh quotient set is bounded below, and nothing produced
it.  Boundedness is exactly a uniform lower bound on the quotients, and two standard mechanisms give
one: an empty sector has no quotient at all, and a form dominating a positive multiple of the norm
gives the multiple as the bound.  In particular a nonnegative form over a positive norm has
nonnegative Rayleigh floor.
-/

namespace GaloisForLFunctions
namespace RHTower

variable {V : Type*}

/-- **A uniform lower bound on the quotients bounds the Rayleigh set below.** -/
theorem bddBelow_rayleighQuotientSet_of_le {Q N : V → ℝ} {D : Set V} {c : ℝ}
    (h : ∀ v ∈ D, N v ≠ 0 → c ≤ Q v / N v) : BddBelow (rayleighQuotientSet Q N D) := by
  refine ⟨c, ?_⟩
  rintro r ⟨v, hv, hN, rfl⟩
  exact h v hv hN

/-- **A form dominating a multiple of a positive norm has a bounded Rayleigh set.** -/
theorem bddBelow_rayleighQuotientSet_of_pos {Q N : V → ℝ} {D : Set V} {c : ℝ}
    (hN : ∀ v ∈ D, 0 < N v) (hQ : ∀ v ∈ D, c * N v ≤ Q v) :
    BddBelow (rayleighQuotientSet Q N D) := by
  refine bddBelow_rayleighQuotientSet_of_le (c := c) fun v hv _ => ?_
  rw [le_div_iff₀ (hN v hv)]
  exact hQ v hv

/-- A nonnegative form over a positive norm has a Rayleigh set bounded below by zero. -/
theorem bddBelow_rayleighQuotientSet_of_nonneg {Q N : V → ℝ} {D : Set V}
    (hN : ∀ v ∈ D, 0 < N v) (hQ : ∀ v ∈ D, 0 ≤ Q v) :
    BddBelow (rayleighQuotientSet Q N D) := by
  refine bddBelow_rayleighQuotientSet_of_pos (c := 0) hN fun v hv => ?_
  rw [zero_mul]
  exact hQ v hv

/-- The empty sector carries no Rayleigh quotient, so its set is bounded below. -/
theorem bddBelow_rayleighQuotientSet_empty (Q N : V → ℝ) :
    BddBelow (rayleighQuotientSet Q N (∅ : Set V)) :=
  bddBelow_rayleighQuotientSet_of_le (c := 0) fun _ hv => absurd hv (Set.notMem_empty _)

end RHTower
end GaloisForLFunctions
