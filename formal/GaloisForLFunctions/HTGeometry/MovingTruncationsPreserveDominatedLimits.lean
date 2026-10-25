import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
One summable envelope permits pointwise limits under independently increasing
finite truncations. Zero-extension turns each truncated sum into a series to
which dominated convergence applies.
-/

open Finset Filter
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.HTGeometry
set_option autoImplicit false

/-- A common summable envelope permits termwise limits and independently growing finite horizons. -/
theorem tendsto_sum_Icc_at_moving_horizon_of_summable_bound
    {f : ℕ → ℕ → ℝ} {g b : ℕ → ℝ} {H : ℕ → ℕ}
    (hH : Tendsto H atTop atTop) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hg0 : g 0 = 0) (hbound : ∀ t n, |f t n| ≤ b n)
    (hpoint : ∀ n, Tendsto (fun t => f t n) atTop (𝓝 (g n))) :
    Tendsto (fun t => ∑ n ∈ Icc 1 (H t), f t n) atTop (𝓝 (∑' n, g n)) := by
  let c : ℕ → ℕ → ℝ := fun t n => if n ∈ Icc 1 (H t) then f t n else 0
  have hcpoint (n : ℕ) : Tendsto (fun t => c t n) atTop (𝓝 (g n)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa only [c, mem_Icc, show ¬ 1 ≤ (0 : ℕ) by decide, false_and, if_false, hg0]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have heq : ∀ᶠ t : ℕ in atTop, c t n = f t n := by
        filter_upwards [hH.eventually_ge_atTop n] with t ht
        exact if_pos (mem_Icc.mpr ⟨hn, ht⟩)
      exact (tendsto_congr' heq).mpr (hpoint n)
  have hcbound : ∀ᶠ t : ℕ in atTop, ∀ n, ‖c t n‖ ≤ b n := by
    apply Eventually.of_forall
    intro t n
    dsimp only [c]
    split_ifs with hn
    · simpa only [Real.norm_eq_abs] using hbound t n
    · simpa only [norm_zero] using hb0 n
  have hlim := tendsto_tsum_of_dominated_convergence hb hcpoint hcbound
  have heq (t : ℕ) : (∑' n, c t n) = ∑ n ∈ Icc 1 (H t), f t n := by
    rw [tsum_eq_sum (s := Icc 1 (H t)) (fun n hn => by simp only [c, if_neg hn])]
    exact sum_congr rfl fun n hn => if_pos hn
  simpa only [heq] using hlim

#print axioms tendsto_sum_Icc_at_moving_horizon_of_summable_bound
end GaloisForLFunctions.HTGeometry
