/-
# The Julia-frontier swap dichotomy (A5)

`BottcherDetermines.c_eq_of_filledJulia_eq'` already gives, unconditionally, that the filled Julia set
determines the parameter: `K_{c₁} = K_{c₂} ⟹ c₁ = c₂`.  This file draws the corollary the relative
hRigid assembly needs: for **distinct** parameters the frontier of one filled Julia set is *not*
contained in the other,

> `c₁ ≠ c₂ ⟹ J_{c₁} ⊄ K_{c₂}  ∨  J_{c₂} ⊄ K_{c₁}`   (`J_c = ∂K_c`),

so at least one orientation supplies a **dendrite/boundary tip `z₀ ∈ J_{c₁} ∖ K_{c₂}`** — a Julia
point of `c₁` lying in the basin of `c₂`, exactly where the relative coefficients
`aᵢ(z) = Qᵢ(z, φ_{c₂}(z))` stay analytic (`φ_{c₂}` continues off `K_{c₂}`).

The engine is a pure plane-topology fact (`subset_of_frontier_subset`): a **full** compact set — one
whose complement is connected and unbounded, as every `K_c` is (`isPreconnected_compl_filledJulia`,
`not_isBounded_basin`) — contains any set whose frontier it contains.  The frontier being inside `L`
confines the connected complement `Lᶜ` to the disjoint open pair `interior K ⊔ Kᶜ`; unboundedness
picks the `Kᶜ` side, giving `K ⊆ L`.  Applying it both ways forces `K₁ = K₂`, contradicting
`c₁ ≠ c₂`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.BottcherDetermines
import GaloisForLFunctions.Bottcher.BasinConnected
import GaloisForLFunctions.Bottcher.Dynamics
import GaloisForLFunctions.Bottcher.BottcherBasin

open Set

namespace Bottcher

/-- **A full compact set contains any subset whose frontier it contains.** If `K` is closed and
bounded and `L` has connected, unbounded complement, then `frontier K ⊆ L ⟹ K ⊆ L`.  The complement
`Lᶜ` avoids `frontier K`, so it splits into the two disjoint opens `interior K` and `Kᶜ`; being
connected it lies in one, and being unbounded (while `interior K ⊆ K` is bounded) it lies in `Kᶜ` —
that is `K ⊆ L`. -/
theorem subset_of_frontier_subset {K L : Set ℂ}
    (hKcl : IsClosed K) (hKbd : Bornology.IsBounded K)
    (hLpc : IsPreconnected Lᶜ) (hLunb : ¬ Bornology.IsBounded Lᶜ)
    (hfr : frontier K ⊆ L) : K ⊆ L := by
  have hfc : (frontier K)ᶜ = interior K ∪ Kᶜ := by
    rw [frontier, hKcl.closure_eq]; ext x; simp only [Set.mem_diff, mem_compl_iff,
      mem_union]; tauto
  have hcover : Lᶜ ⊆ interior K ∪ Kᶜ := by
    rw [← hfc]; exact compl_subset_compl.mpr hfr
  have hdisj : Disjoint (interior K) Kᶜ :=
    Set.disjoint_left.mpr (fun x hx hxc => hxc (interior_subset hx))
  rcases hLpc.subset_or_subset isOpen_interior hKcl.isOpen_compl hdisj hcover with hInt | hKc
  · -- `Lᶜ ⊆ interior K` would make the unbounded `Lᶜ` bounded
    exact absurd ((hKbd.subset interior_subset).subset hInt) hLunb
  · -- `Lᶜ ⊆ Kᶜ` is exactly `K ⊆ L`
    exact compl_subset_compl.mp hKc

/-- **The Julia-frontier swap dichotomy.** For distinct parameters, at least one filled Julia set does
not contain the other's Julia frontier.  Otherwise `subset_of_frontier_subset` (both filled Julia sets
are full — `isPreconnected_compl_filledJulia`, `not_isBounded_basin`) forces `K_{c₁} = K_{c₂}`, whence
`c₁ = c₂` by `c_eq_of_filledJulia_eq'`. -/
theorem juliaFrontier_swap_dichotomy {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂) :
    ¬ (frontier (filledJulia c₁) ⊆ filledJulia c₂) ∨
    ¬ (frontier (filledJulia c₂) ⊆ filledJulia c₁) := by
  by_contra h
  push Not at h
  obtain ⟨h12, h21⟩ := h
  have hunb : ∀ c : ℂ, ¬ Bornology.IsBounded (filledJulia c)ᶜ := by
    intro c; rw [← basin_eq_compl_filledJulia]; exact not_isBounded_basin c
  have hK12 : filledJulia c₁ ⊆ filledJulia c₂ :=
    subset_of_frontier_subset (isClosed_filledJulia c₁) (isBounded_filledJulia c₁)
      (isPreconnected_compl_filledJulia c₂) (hunb c₂) h12
  have hK21 : filledJulia c₂ ⊆ filledJulia c₁ :=
    subset_of_frontier_subset (isClosed_filledJulia c₂) (isBounded_filledJulia c₂)
      (isPreconnected_compl_filledJulia c₁) (hunb c₁) h21
  exact hne (c_eq_of_filledJulia_eq' (subset_antisymm hK12 hK21))

/-- **Existence form: a tip in one Julia frontier lying in the other basin.** For distinct parameters
there is a Julia point of one that escapes the other — the boundary tip `z₀ ∈ J_{c₁} ∩ K_{c₂}ᶜ` (or
swapped) that the relative dendrite obstruction consumes. -/
theorem exists_juliaFrontier_mem_compl_other {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂) :
    (∃ z ∈ frontier (filledJulia c₁), z ∈ (filledJulia c₂)ᶜ) ∨
    (∃ z ∈ frontier (filledJulia c₂), z ∈ (filledJulia c₁)ᶜ) := by
  rcases juliaFrontier_swap_dichotomy hne with h | h
  · exact Or.inl (by simpa [Set.not_subset] using h)
  · exact Or.inr (by simpa [Set.not_subset] using h)

end Bottcher
