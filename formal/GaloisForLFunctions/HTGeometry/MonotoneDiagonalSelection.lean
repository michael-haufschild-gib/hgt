import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Data.Nat.Find

/-! Row convergence to a countably generated filter admits a slow monotone diagonal. -/

open Filter

namespace GaloisForLFunctions.HTGeometry

theorem exists_monotone_diagonal_tendsto {α : Type*} {l : Filter α}
    [IsCountablyGenerated l] (F : ℕ → ℕ → α)
    (hF : ∀ n, Tendsto (F n) atTop l) :
    ∃ m : ℕ → ℕ, Monotone m ∧ (∀ r, m r ≤ r) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun r => F (m r) r) atTop l := by
  classical
  obtain ⟨s, hs⟩ := exists_antitone_basis l
  have hevent (n : ℕ) : ∃ N : ℕ, ∀ r, N ≤ r → F n r ∈ s n :=
    eventually_atTop.mp ((hs.toHasBasis.tendsto_right_iff.mp (hF n)) n trivial)
  choose T hT using hevent
  let m (r : ℕ) : ℕ := Nat.findGreatest (fun n => T n ≤ r) r
  have hmono : Monotone m := by
    intro r R hrR
    exact Nat.findGreatest_mono (fun n hn => hn.trans hrR) hrR
  have hle (r : ℕ) : m r ≤ r := Nat.findGreatest_le r
  have htop : Tendsto m atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro n
    refine ⟨max n (T n), fun r hr => ?_⟩
    exact Nat.le_findGreatest ((le_max_left _ _).trans hr) ((le_max_right _ _).trans hr)
  refine ⟨m, hmono, hle, htop, hs.toHasBasis.tendsto_right_iff.mpr ?_⟩
  intro n _
  filter_upwards [htop.eventually (eventually_ge_atTop n), eventually_ge_atTop (T 0)] with r hn h0
  have hmvalid : T (m r) ≤ r :=
    Nat.findGreatest_spec (P := fun n => T n ≤ r) (Nat.zero_le r) h0
  exact hs.antitone hn (hT (m r) r hmvalid)

end GaloisForLFunctions.HTGeometry
