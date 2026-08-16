import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection

/-!
# Quantitative rigidity from a kernel

A linear map out of a finite-dimensional normed space is bounded below on a complement of its
kernel, so the distance of a point to the kernel is controlled by the norm of its image.
-/

open Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **A linear map controls the distance to its kernel.** -/
theorem exists_pos_infDist_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ[ℝ] F) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x : E, γ * Metric.infDist x (LinearMap.ker T : Set E) ≤ ‖T x‖ := by
  classical
  obtain ⟨W, hW⟩ := (LinearMap.ker T).exists_isCompl
  have hinj : (T.comp W.subtype).ker = ⊥ := by
    refine le_antisymm (fun w hw => ?_) bot_le
    have hker : (w : E) ∈ LinearMap.ker T := LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hw)
    have := Submodule.disjoint_def.mp hW.disjoint (w : E) hker w.2
    exact Submodule.mem_bot _ |>.mpr (Subtype.ext this)
  obtain ⟨K, hK, hanti⟩ := (T.comp W.subtype).exists_antilipschitzWith hinj
  refine ⟨1 / K, by positivity, fun x => ?_⟩
  have hsup : x ∈ LinearMap.ker T ⊔ W := by
    rw [hW.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.mp hsup
  have hTx : T x = T w := by
    rw [← hkw, map_add, LinearMap.mem_ker.mp hk, zero_add]
  have hnorm : ‖w‖ ≤ (K : ℝ) * ‖T w‖ := by
    have := hanti.le_mul_dist ⟨w, hw⟩ 0
    simpa [dist_eq_norm] using this
  have hdist : Metric.infDist x (LinearMap.ker T : Set E) ≤ ‖w‖ := by
    have hmem : k ∈ (LinearMap.ker T : Set E) := hk
    have hle : Metric.infDist x (LinearMap.ker T : Set E) ≤ dist x k :=
      Metric.infDist_le_dist_of_mem hmem
    rw [dist_eq_norm] at hle
    have hxk : x - k = w := by rw [← hkw]; abel
    rwa [hxk] at hle
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by exact_mod_cast hK)]
  calc Metric.infDist x (LinearMap.ker T : Set E) ≤ ‖w‖ := hdist
    _ ≤ (K : ℝ) * ‖T w‖ := hnorm
    _ = ‖T x‖ * K := by rw [hTx]; ring

end GaloisForLFunctions.HTGeometry
