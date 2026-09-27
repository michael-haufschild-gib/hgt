import GaloisForLFunctions.RHTower.LogarithmicEntryIntegration
import Mathlib.Topology.Piecewise

/-!
# Continuous logarithmic entry sums

A moving integer cutoff preserves continuity when each profile vanishes
at its own entry time. On every neighborhood the sum has a fixed finite
prefix; no infinite convergence theorem is needed.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace RHTower

def logarithmicVariableEntrySum (f : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f n t

theorem logarithmicVariableEntrySum_eq_common_prefix (f : ℕ → ℝ → ℝ)
    {T t : ℝ} (ht : t ≤ T) :
    logarithmicVariableEntrySum f t =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (Ici (Real.log n)).indicator (f n) t := by
  simpa only [logarithmicEntrySum, logarithmicVariableEntrySum, indicator_apply] using
    logarithmicEntrySum_eq_common_prefix (fun n => f n t) ht

theorem continuous_logarithmicVariableEntrySum (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, 1 ≤ n → Continuous (f n))
    (hz : ∀ n, 1 ≤ n → f n (Real.log n) = 0) :
    Continuous (logarithmicVariableEntrySum f) := by
  classical
  have hi (n : ℕ) (hn : 1 ≤ n) :
      Continuous ((Ici (Real.log n)).indicator (f n)) := by
    apply Continuous.piecewise _ (hf n hn) continuous_const
    intro t ht
    have ht' : t = Real.log n := by simpa only [frontier_Ici, mem_singleton_iff] using ht
    simpa only [ht'] using hz n hn
  rw [continuous_iff_continuousAt]
  intro t
  have hc : Continuous (fun u : ℝ =>
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (t + 1)⌋₊, (Ici (Real.log n)).indicator (f n) u) :=
    continuous_finsetSum _ (fun n hn => hi n (Finset.mem_Icc.mp hn).1)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (show t < t + 1 by linarith)] with u hu
  exact logarithmicVariableEntrySum_eq_common_prefix f (le_of_lt hu)

end RHTower
