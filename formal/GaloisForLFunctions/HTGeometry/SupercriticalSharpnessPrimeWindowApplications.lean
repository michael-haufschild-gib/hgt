import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms

/-!
# Supercritical sharpness mechanisms for disjoint prime windows

At unit phase, multiplicative prime windows form a concrete disjoint family.  The paper's
disjoint-ball mass collection and finite-slab density steps therefore become exact finite identities
and an average-heavy-window selector.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Classical

private theorem unitPrimeWindows_pairwiseDisjoint (M : ℕ) :
    ((Finset.range M : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun m ↦ primesInIoc (winLoNat 1 m) (winHiNat 1 m)) := by
  intro a _ b _ hab
  exact primesInIoc_window_disjoint (by norm_num) hab

/-- The cardinality of first `M` unit-phase prime windows is exact additive mass because windows
are pairwise disjoint. -/
theorem card_unitPrimeWindow_biUnion_eq_sum (M : ℕ) :
    ((Finset.range M).biUnion
      (fun m ↦ primesInIoc (winLoNat 1 m) (winHiNat 1 m))).card =
        ∑ m ∈ Finset.range M, (primesInIoc (winLoNat 1 m) (winHiNat 1 m)).card := by
  rw [Finset.card_biUnion (unitPrimeWindows_pairwiseDisjoint M)]

/-- The leading-term mass over first `M` unit-phase windows is exactly mass over their disjoint
union. -/
theorem sum_unitPrimeWindows_eq_sum_biUnion (σ : ℝ) (M : ℕ) :
    ∑ m ∈ Finset.range M, windowSum σ 1 m =
      ∑ n ∈ (Finset.range M).biUnion
        (fun m ↦ primesInIoc (winLoNat 1 m) (winHiNat 1 m)), leadingTerm σ 1 n := by
  rw [Finset.sum_biUnion (unitPrimeWindows_pairwiseDisjoint M)]
  exact Finset.sum_congr rfl fun m _ ↦ windowSum_eq_sum_leadingTerm σ 1 m

/-- Among first `M` unit-phase prime windows, either there are none or one carries at least average
window mass. -/
theorem unitPrimeWindowSum_empty_or_averageHeavy (σ : ℝ) (M : ℕ) :
    M = 0 ∨ ∃ m : Fin M,
      (∑ j : Fin M, windowSum σ 1 j) ≤ (M : ℝ) * windowSum σ 1 m := by
  simpa only [Fintype.card_fin] using
    (finiteFamilySum_empty_or_le_card_mul (fun m : Fin M ↦ windowSum σ 1 m))

end GaloisForLFunctions.HTGeometry
