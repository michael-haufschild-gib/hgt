import GaloisForLFunctions.RHTower.LegMidpointPush
import GaloisForLFunctions.RHTower.LegStripEquilibrium

/-!
# Existence and midpoint location of structured Leg equilibria

The structured decreasing-gap estimate located an equilibrium only after one was supplied.  The
pole blow-up theorem independently constructs an equilibrium in every pole-free gap with simple
endpoint poles.  On the structured two-train configuration, these mechanisms combine to remove
the hypothetical-root premise and force a genuine equilibrium past the midpoint.
-/

open Real Set

namespace RHTower

open Finset

noncomputable section

/-- **Structured Leg midpoint-equilibrium universality law.**  For a two-train configuration with
simple gap-edge poles, the paired-deficit budget produces an actual equilibrium at the prescribed
Leg level, and every such constructed equilibrium lies strictly to the right of the gap midpoint. -/
theorem exists_structuredLegEquilibrium_pushed_past_midpoint
    {M E : ℕ} {t : ℕ → ℝ} {a b : ℝ} (hab : a < b)
    (hpB : ∀ k ∈ range M, t k ≤ a)
    (hpA : ∀ k ∈ range M, b ≤ t (M + k))
    (hpair : ∀ k ∈ range M,
      t (M + k) - (a + b) / 2 ≤ (a + b) / 2 - t k)
    (hpX : ∀ j ∈ range E, t (2 * M + j) ≤ a)
    (hea : t (2 * M + E) = a) (heb : t (2 * M + E + 1) = b)
    (hsimpleA : ∀ k ∈ range (2 * M + E + 2),
      k ≠ 2 * M + E → t k ≠ a)
    (hsimpleB : ∀ k ∈ range (2 * M + E + 2),
      k ≠ 2 * M + E + 1 → t k ≠ b)
    (hbudget : (∑ k ∈ range M,
        ((((a + b) / 2 - t k) - (t (M + k) - (a + b) / 2)) / 2) *
          (rcsch ((t (M + k) - (a + b) / 2) / 2)) ^ 2)
      < 2 * (M : ℝ) + 2 * E + 2) :
    ∃ x ∈ Ioo a b,
      cothField (range (2 * M + E + 2)) t x =
          -(2 * (M : ℝ) + E + 2) ∧
        b - x < (b - a) / 2 := by
  have hpoles : ∀ k ∈ range (2 * M + E + 2),
      t k ≤ a ∨ b ≤ t k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rcases Nat.lt_or_ge k M with h1 | h1
    · exact Or.inl (hpB k (Finset.mem_range.mpr h1))
    rcases Nat.lt_or_ge k (2 * M) with h2 | h2
    · right
      have hkform : k = M + (k - M) := by omega
      rw [hkform]
      exact hpA (k - M) (Finset.mem_range.mpr (by omega))
    rcases Nat.lt_or_ge k (2 * M + E) with h3 | h3
    · left
      have hkform : k = 2 * M + (k - 2 * M) := by omega
      rw [hkform]
      exact hpX (k - 2 * M) (Finset.mem_range.mpr (by omega))
    by_cases hedge : k = 2 * M + E
    · left
      rw [hedge, hea]
    · right
      have hkedge : k = 2 * M + E + 1 := by omega
      rw [hkedge, heb]
  have hkA : 2 * M + E ∈ range (2 * M + E + 2) :=
    Finset.mem_range.mpr (by omega)
  have hkB : 2 * M + E + 1 ∈ range (2 * M + E + 2) :=
    Finset.mem_range.mpr (by omega)
  obtain ⟨x, hx, heq⟩ := cothField_root_exists
    (range (2 * M + E + 2)) t hab hpoles hkA hea hsimpleA hkB heb hsimpleB
      (-(2 * (M : ℝ) + E + 2))
  refine ⟨x, hx, heq, ?_⟩
  exact midpoint_push_of_deficit hab hpB hpA hpair hpX hea heb hbudget hx heq

end

end RHTower
