import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity
import Mathlib.GroupTheory.Solvable

/-!
# The radical regime of the critical horizon

The number of critical states of a two-horizon observation is a binomial coefficient.  It is at most
four exactly at the five smallest horizon pairs: one side must have depth one, and the other depth
at most three.

Every genuinely two-sided horizon has at least six states, so its symmetric group is not solvable and
the generic state equation is not solvable by radicals.
-/

namespace GaloisForLFunctions.HTGeometry

theorem choose_left_one (n : ℕ) : (1 + n).choose 1 = 1 + n :=
  Nat.choose_one_right _

theorem choose_right_self (m : ℕ) : (m + 1).choose m = m + 1 := by
  have h : (m + 1).choose ((m + 1) - m) = (m + 1).choose m := Nat.choose_symm (by omega)
  rw [show (m + 1) - m = 1 by omega, Nat.choose_one_right] at h
  exact h.symm

/-- **The radical regime of the critical horizon.**  The critical multiplicity is at most four
exactly when one depth is one and the other is at most three. -/
theorem criticalHorizonMultiplicity_le_four_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalHorizonMultiplicity m n ≤ 4 ↔ (m = 1 ∧ n ≤ 3) ∨ (n = 1 ∧ m ≤ 3) := by
  rw [criticalHorizonMultiplicity]
  constructor
  · intro hle
    by_cases hm2 : 2 ≤ m
    · by_cases hn2 : 2 ≤ n
      · exact absurd hle (by
          have := criticalHorizonMultiplicity_ge_six hm2 hn2
          rw [criticalHorizonMultiplicity] at this
          omega)
      · refine Or.inr ⟨by omega, ?_⟩
        have hn1 : n = 1 := by omega
        subst hn1
        rw [choose_right_self] at hle
        omega
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [choose_left_one] at hle
      exact Or.inl ⟨rfl, by omega⟩
  · rintro (⟨rfl, hn3⟩ | ⟨rfl, hm3⟩)
    · rw [choose_left_one]
      omega
    · rw [choose_right_self]
      omega

/-- **The five radical horizon pairs.** -/
theorem criticalHorizonMultiplicity_le_four_iff_mem {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalHorizonMultiplicity m n ≤ 4 ↔
      (m = 1 ∧ n = 1) ∨ (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) ∨
        (m = 1 ∧ n = 3) ∨ (m = 3 ∧ n = 1) := by
  rw [criticalHorizonMultiplicity_le_four_iff hm hn]
  constructor
  · rintro (⟨rfl, hn3⟩ | ⟨rfl, hm3⟩)
    · interval_cases n
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · interval_cases m
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

/-- **A genuinely two-sided horizon is outside the radical regime.**  Its symmetric group on the
critical states is not solvable. -/
theorem not_isSolvable_perm_criticalStates {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ IsSolvable (Equiv.Perm (Fin (criticalHorizonMultiplicity m n))) := by
  refine Equiv.Perm.not_solvable _ ?_
  have h6 := criticalHorizonMultiplicity_ge_six hm hn
  rw [Cardinal.mk_fin]
  exact_mod_cast (by omega : 5 ≤ criticalHorizonMultiplicity m n)

end GaloisForLFunctions.HTGeometry
