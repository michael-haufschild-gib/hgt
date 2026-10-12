import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.PartialSups

/-! Eventually convergent rows admit a monotone diagonal dominating the row index. -/

open Filter

namespace GaloisForLFunctions.HTGeometry

theorem exists_monotone_fast_diagonal_tendsto {α : Type*} {l : Filter α}
    [IsCountablyGenerated l] (F : ℕ → ℕ → α)
    (hF : ∀ᶠ r in atTop, Tendsto (F r) atTop l) :
    ∃ m : ℕ → ℕ, Monotone m ∧ (∀ r, r ≤ m r) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun r => F r (m r)) atTop l := by
  classical
  obtain ⟨s, hs⟩ := exists_antitone_basis l
  have hchoice (r : ℕ) : ∃ N : ℕ, Tendsto (F r) atTop l →
      ∀ n, N ≤ n → F r n ∈ s r := by
    by_cases hrow : Tendsto (F r) atTop l
    · obtain ⟨N, hN⟩ := eventually_atTop.mp
        ((hs.toHasBasis.tendsto_right_iff.mp hrow) r trivial)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => False.elim (hrow h)⟩
  choose N hN using hchoice
  let m (r : ℕ) := max r (partialSups N r)
  have hmono : Monotone m := by
    intro r R hrR
    exact max_le_max hrR ((partialSups N).monotone hrR)
  have hge (r : ℕ) : r ≤ m r := le_max_left _ _
  have htop : Tendsto m atTop atTop := tendsto_atTop_mono hge tendsto_id
  refine ⟨m, hmono, hge, htop, hs.toHasBasis.tendsto_right_iff.mpr ?_⟩
  intro k _
  filter_upwards [eventually_ge_atTop k, hF] with r hkr hrow
  exact hs.antitone hkr (hN r hrow (m r) ((le_partialSups N r).trans (le_max_right _ _)))

end GaloisForLFunctions.HTGeometry
