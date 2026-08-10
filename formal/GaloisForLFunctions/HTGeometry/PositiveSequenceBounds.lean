import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Uniform positive bounds for a convergent positive sequence

A strictly positive sequence with a strictly positive limit is trapped between two strictly
positive constants: the upper bound is boundedness of a convergent sequence, and the lower bound
combines the eventual bound `L/2` with the minimum over the finitely many exceptional indices.

This turns an asymptotic of the form `a n → L > 0` into the uniform two-sided estimate that
tail summations need.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- A strictly positive sequence converging to a strictly positive limit is bounded above and
below by strictly positive constants. -/
theorem exists_pos_bounds_of_tendsto_pos {a : ℕ → ℝ} {L : ℝ} (hL : 0 < L)
    (hpos : ∀ n, 0 < a n) (h : Tendsto a atTop (nhds L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n, c ≤ a n ∧ a n ≤ C := by
  classical
  obtain ⟨C, hC⟩ := h.bddAbove_range
  have hub : ∀ n, a n ≤ C := fun n => hC (Set.mem_range_self n)
  have hev : ∀ᶠ n in atTop, L / 2 < a n :=
    h.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set S : Finset ℕ := Finset.range (N + 1) with hS
  have hSne : S.Nonempty := ⟨0, by simp [hS]⟩
  set c : ℝ := S.inf' hSne (fun i => min (a i) (L / 2)) with hc
  have hcpos : 0 < c := by
    rw [hc, Finset.lt_inf'_iff]
    intro i _
    exact lt_min (hpos i) (by linarith)
  have hczero : c ≤ min (a 0) (L / 2) := by
    rw [hc]
    exact Finset.inf'_le _ (by simp [hS])
  have hcle : ∀ n, c ≤ a n := by
    intro n
    by_cases hn : n ≤ N
    · have hmem : n ∈ S := by simp [hS]; omega
      exact le_trans (by rw [hc]; exact Finset.inf'_le _ hmem) (min_le_left _ _)
    · have hcL : c ≤ L / 2 := le_trans hczero (min_le_right _ _)
      exact le_of_lt (lt_of_le_of_lt hcL (hN n (by omega)))
  exact ⟨c, C, hcpos, lt_of_lt_of_le hcpos (hub 0 |> le_trans (hcle 0)), fun n => ⟨hcle n, hub n⟩⟩

end GaloisForLFunctions
