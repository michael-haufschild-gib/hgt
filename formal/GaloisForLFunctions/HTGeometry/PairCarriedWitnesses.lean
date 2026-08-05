import GaloisForLFunctions.HTGeometry.MultipleGammaAnnihilatorExact

/-!
# Carried face pairs exist

A face pair is carried when its complement has at least two members and its exponent vector is
supported inside the face.  The empty face with the zero exponent is carried as soon as the index
set has at least two members, and being carried is inherited by every exponent vector supported in
the same face — so the annihilator packet is nonempty in every corank at least two.
-/

namespace GaloisForLFunctions

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The empty face with the zero exponent is carried,** whenever the index set has at least two
members. -/
theorem pairCarried_empty (h : 2 ≤ Fintype.card ι) :
    PairCarried ((∅ : Finset ι), (0 : ι →₀ ℕ)) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.compl_empty, Finset.card_univ]
    exact h
  · simp

/-- Carriedness only constrains the support, so it is inherited by every exponent supported in the
same face. -/
theorem pairCarried_of_support_subset {L : Finset ι} {m : ι →₀ ℕ}
    (hL : 2 ≤ (Lᶜ).card) (hm : m.support ⊆ L) : PairCarried (L, m) :=
  ⟨hL, hm⟩

/-- Carried pairs exist in every corank at least two. -/
theorem exists_pairCarried (h : 2 ≤ Fintype.card ι) :
    ∃ p : Finset ι × (ι →₀ ℕ), PairCarried p :=
  ⟨_, pairCarried_empty h⟩

end GaloisForLFunctions
