import GaloisForLFunctions.HTGeometry.WittFormationMechanics
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Uniform detection by the first power sums

The first `r` positive power sums of an `r`-mode packet vanish together
only at the zero packet. Compactness upgrades this algebraic reconstruction
fact to a uniform positive observation bound on the unit sphere, even
when complex cancellation makes individual power sums vanish.
-/

namespace GaloisForLFunctions.HilbertMetric.Observation

open GaloisForLFunctions.HTGeometry

/-- Total observation supplied by the first positive power sums. -/
noncomputable def finiteGhostMass {r : ℕ} (x : Fin r → ℂ) : ℝ :=
  ∑ k ∈ Finset.range r, ‖wittGhost x (k + 1)‖

/-- Cancellation cannot annihilate every one of the first `r` positive power sums. -/
theorem finiteGhostMass_eq_zero_iff {r : ℕ} (x : Fin r → ℂ) :
    finiteGhostMass x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hz : ∀ k ∈ Finset.range r, wittGhost x (k + 1) = 0 := by
      intro k hk
      have hle : ‖wittGhost x (k + 1)‖ ≤ finiteGhostMass x :=
        Finset.single_le_sum (fun i _ => norm_nonneg _) hk
      rw [hx] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    have he := wittGhost_reconstructs_modes x 0 (by
      intro k hk
      cases k with
      | zero => simp [wittGhost]
      | succ k =>
        rw [hz k (Finset.mem_range.mpr (by omega))]
        simp [wittGhost])
    funext i
    have hi : x i ∈ Finset.univ.val.map x :=
      Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    rw [he] at hi
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hi
    exact hj.symm
  · rintro rfl
    simp [finiteGhostMass, wittGhost]

/-- Every finite power-sum observation depends continuously on the packet. -/
theorem continuous_finiteGhostMass (r : ℕ) :
    Continuous (finiteGhostMass : (Fin r → ℂ) → ℝ) := by
  change Continuous (fun x : Fin r → ℂ =>
    ∑ k ∈ Finset.range r, ‖∑ i : Fin r, x i ^ (k + 1)‖)
  fun_prop

/-- Every normalized packet has a uniformly detectable positive power sum. -/
theorem unitSphere_uniform_ghost_detection (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.sphere (0 : Fin r → ℂ) 1,
      ε ≤ finiteGhostMass x := by
  apply (isCompact_sphere (0 : Fin r → ℂ) 1).exists_forall_le'
    (continuous_finiteGhostMass r).continuousOn
  intro x hx
  have hx0 : x ≠ 0 := by
    intro he
    subst x
    simpa using hx
  have hnonneg : 0 ≤ finiteGhostMass x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact lt_of_le_of_ne hnonneg (Ne.symm ((finiteGhostMass_eq_zero_iff x).not.mpr hx0))

end GaloisForLFunctions.HilbertMetric.Observation

#print axioms GaloisForLFunctions.HilbertMetric.Observation.finiteGhostMass_eq_zero_iff
#print axioms GaloisForLFunctions.HilbertMetric.Observation.unitSphere_uniform_ghost_detection
