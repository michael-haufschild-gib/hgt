import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Lipschitz images cannot fill a higher-dimensional target

A Lipschitz map does not raise Hausdorff dimension, so the image of a subset of an `M`-dimensional
normed space under `r` Lipschitz real functions has Hausdorff dimension at most `M`.  If `M < r`
that image has empty interior in `ℝ^r`, so arbitrarily small vectors are omitted from it.

This is the quantitative half of a topological dimension bound: `r` real observables of an
`M`-dimensional set can be simultaneously perturbed off any prescribed value when `r` exceeds `M`,
however the observables are arranged.
-/

open Set

open scoped ENNReal NNReal

namespace GaloisForLFunctions

/-- The joint image of a set under `r` uniformly Lipschitz real functions has Hausdorff dimension
at most the dimension of the ambient space. -/
theorem dimH_lipschitz_pi_image_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ} {C : NNReal} {u : Fin r → E → ℝ}
    (hu : ∀ j, LipschitzWith C (u j)) (s : Set E) :
    dimH ((fun x => fun j => u j x) '' s) ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
  have hL : LipschitzWith C (fun x : E => fun j => u j x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_pi_le_iff (by positivity)]
    exact fun j => (hu j).dist_le_mul x y
  calc dimH ((fun x => fun j => u j x) '' s) ≤ dimH s := hL.dimH_image_le s
    _ ≤ dimH (univ : Set E) := dimH_mono (subset_univ s)
    _ = (Module.finrank ℝ E : ℝ≥0∞) :=
        Real.dimH_of_mem_nhds (x := (0 : E)) Filter.univ_mem

/-- **Small omitted values.**  If `r` exceeds the dimension of the ambient space, then `r` uniformly
Lipschitz real functions omit values arbitrarily close to the origin: there is a vector `v` of norm
below any prescribed `δ` which is not the joint value of the functions at any point of `s`. -/
theorem exists_norm_lt_notMem_lipschitz_pi_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {r : ℕ} {C : NNReal} {u : Fin r → E → ℝ}
    (hu : ∀ j, LipschitzWith C (u j)) (s : Set E) (hlt : Module.finrank ℝ E < r) {δ : ℝ}
    (hδ : 0 < δ) : ∃ v : Fin r → ℝ, ‖v‖ < δ ∧ ∀ x ∈ s, (fun j => u j x) ≠ v := by
  by_contra hcon
  push Not at hcon
  have hsub : Metric.ball (0 : Fin r → ℝ) δ ⊆ (fun x => fun j => u j x) '' s := by
    intro v hv
    have hnorm : ‖v‖ < δ := by
      have := Metric.mem_ball.mp hv
      rwa [dist_zero_right] at this
    obtain ⟨x, hx, hxv⟩ := hcon v hnorm
    exact ⟨x, hx, hxv⟩
  have hnhds : (fun x => fun j => u j x) '' s ∈ nhds (0 : Fin r → ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds _ hδ) hsub
  have hdim : dimH ((fun x => fun j => u j x) '' s)
      = (Module.finrank ℝ (Fin r → ℝ) : ℝ≥0∞) := Real.dimH_of_mem_nhds hnhds
  rw [Module.finrank_fin_fun] at hdim
  have hle := dimH_lipschitz_pi_image_le hu s
  rw [hdim] at hle
  have : (r : ℝ≥0∞) ≤ (Module.finrank ℝ E : ℝ≥0∞) := hle
  have hlt' : (Module.finrank ℝ E : ℝ≥0∞) < (r : ℝ≥0∞) := by
    exact_mod_cast Nat.cast_lt.mpr hlt
  exact absurd this (not_le.mpr hlt')

end GaloisForLFunctions
