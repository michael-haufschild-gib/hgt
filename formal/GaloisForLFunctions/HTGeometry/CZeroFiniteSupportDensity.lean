import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Finite-support density in `C₀(ℕ, E)`

Natural-coordinate truncations of a function vanishing at infinity have finite support and converge
in the uniform norm.  This is the concrete `c₀₀`-density statement needed by locally C*-algebra
closure arguments.
-/

open Filter Topology
open scoped ZeroAtInfty

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- Retain the first `n` coordinates of a `C₀(ℕ,E)` function. -/
def cZeroNatTruncation (f : C₀(ℕ, E)) (n : ℕ) : C₀(ℕ, E) where
  toFun k := if k < n then f k else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [eventually_ge_atTop n] with k hk
    simp [Nat.not_lt.mpr hk]

@[simp] theorem cZeroNatTruncation_apply (f : C₀(ℕ, E)) (n k : ℕ) :
    cZeroNatTruncation f n k = if k < n then f k else 0 := rfl

/-- Every natural-coordinate truncation has finite support. -/
theorem cZeroNatTruncation_support_finite (f : C₀(ℕ, E)) (n : ℕ) :
    Set.Finite (Function.support (cZeroNatTruncation f n)) := by
  apply (Finset.finite_toSet (Finset.range n)).subset
  intro k hk
  simp only [Function.mem_support] at hk
  have hkn : k < n := by
    by_contra h
    exact hk (by simp [cZeroNatTruncation_apply, Nat.not_lt.mp h])
  simpa using hkn

/-- The finite-support natural-coordinate truncations converge in the uniform norm. -/
theorem tendsto_cZeroNatTruncation (f : C₀(ℕ, E)) :
    Tendsto (cZeroNatTruncation f) atTop (nhds f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf : Tendsto f atTop (nhds 0) := by
    simpa [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty f
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hf) (ε / 2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  have hop : ‖f - cZeroNatTruncation f n‖ ≤ ε / 2 := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (by linarith)).mpr
    intro k
    by_cases hk : k < n
    · simpa [cZeroNatTruncation_apply, hk] using (show 0 ≤ ε / 2 by linarith)
    · have hNk : N ≤ k := hn.trans (Nat.le_of_not_gt hk)
      have htail := hN k hNk
      rw [dist_zero_right] at htail
      simpa [cZeroNatTruncation_apply, hk] using le_of_lt htail
  simpa [norm_sub_rev] using hop.trans_lt (by linarith)

end
end GaloisForLFunctions.HTGeometry
