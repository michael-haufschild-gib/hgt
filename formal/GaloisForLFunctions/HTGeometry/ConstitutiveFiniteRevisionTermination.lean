import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic

/-!
# Finite monotone compatibility revision terminates

No infinite sequence can strictly add compatibility facts at every active step when the vocabulary
of possible facts is finite.  A finite monotone revision process is saturation, not open genesis.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {Edge : Type u} [Fintype Edge]

/-- A finite compatibility vocabulary admits no infinite strictly increasing active history. -/
theorem constitutiveNoInfiniteStrictFiniteRevision
    (history : ℕ → Finset Edge)
    (hstep : ∀ n, history n < history (n + 1)) : False := by
  have hstrict : StrictMono history := strictMono_nat_of_lt_succ hstep
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (α := ℕ) history
  exact hij (hstrict.injective heq)

/-- Every monotone finite-vocabulary history has a stable adjacent step. -/
theorem constitutiveFiniteMonotoneRevision_has_stable_step
    (history : ℕ → Finset Edge)
    (hmono : ∀ n, history n ⊆ history (n + 1)) :
    ∃ n, history n = history (n + 1) := by
  by_contra hstable
  push Not at hstable
  apply constitutiveNoInfiniteStrictFiniteRevision history
  intro n
  exact lt_of_le_of_ne (hmono n) (hstable n)

/-- Closed capstone for the finite monotone termination boundary. -/
theorem constitutiveFiniteRevisionTerminationMechanism_closed :
    (∀ history : ℕ → Finset Edge,
      (∀ n, history n < history (n + 1)) → False) ∧
    (∀ history : ℕ → Finset Edge,
      (∀ n, history n ⊆ history (n + 1)) →
        ∃ n, history n = history (n + 1)) := by
  exact ⟨constitutiveNoInfiniteStrictFiniteRevision,
    constitutiveFiniteMonotoneRevision_has_stable_step⟩

end GaloisForLFunctions.HTGeometry
