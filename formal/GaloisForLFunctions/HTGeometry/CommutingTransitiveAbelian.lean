import Mathlib.GroupTheory.GroupAction.Basic

/-!
# A free action commuting with a transitive abelian action is abelian
-/

namespace GaloisForLFunctions.HTGeometry

variable {P G M : Type*} [Group G] [Group M] [MulAction G P] [MulAction M P]

/-- **Transport of commutativity across two commuting actions.**  If `G` has an injective orbit map
at `x₀`, if `M` reaches every point from `x₀`, and if the two actions commute elementwise, then
commutativity of `M` forces commutativity of `G`.

This is the deck-group/monodromy comparison: for a connected covering the deck group acts with
injective orbit map, the monodromy acts transitively, the two commute, and the monodromy of a
covering of a topological group is abelian. -/
theorem mul_comm_of_commuting_transitive_of_mul_comm (x₀ : P)
    (hfree : ∀ g h : G, g • x₀ = h • x₀ → g = h)
    (htrans : ∀ y : P, ∃ μ : M, μ • x₀ = y)
    (hcomm : ∀ (g : G) (μ : M) (x : P), μ • (g • x) = g • (μ • x))
    (hab : ∀ μ ν : M, μ * ν = ν * μ) (g h : G) :
    g * h = h * g := by
  obtain ⟨μg, hμg⟩ := htrans (g • x₀)
  obtain ⟨μh, hμh⟩ := htrans (h • x₀)
  refine hfree _ _ ?_
  have e1 : (μg * μh) • x₀ = (h * g) • x₀ := by
    rw [mul_smul, hμh, hcomm, hμg, ← mul_smul]
  have e2 : (μh * μg) • x₀ = (g * h) • x₀ := by
    rw [mul_smul, hμg, hcomm, hμh, ← mul_smul]
  rw [← e2, ← e1, hab]

end GaloisForLFunctions.HTGeometry
