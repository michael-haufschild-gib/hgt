import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Group.CocompactMap
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open Metric Set Filter Topology
namespace GaloisForLFunctions.HTGeometry

/-- A continuous positive-degree homogeneous map with trivial zero fiber is uniformly separated
from zero on all rays. Properness of the source makes the unit sphere compact. -/
theorem exists_homogeneous_norm_lower_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : E → F) (hH : Continuous H) (d : ℕ) (hd : 0 < d)
    (hhom : ∀ (r : ℝ), 0 < r → ∀ x, H (r • x) = r ^ d • H x)
    (hzero : ∀ x, H x = 0 → x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ d ≤ ‖H x‖ := by
  obtain ⟨c, hc, hbound⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hH.norm.continuousOn (a := (0 : ℝ)) (by
      intro x hx
      apply norm_pos_iff.mpr
      intro hh
      have hx0 := hzero x hh
      simp [hx0] at hx)
  refine ⟨c, hc, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, zero_pow hd.ne']
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : E := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_cancel₀ hr.ne']
  have hry : ‖x‖ • y = x := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hh := hhom ‖x‖ hr y
  rw [hry] at hh
  rw [hh, norm_smul, Real.norm_of_nonneg (pow_nonneg hr.le d)]
  have hcy : c ≤ ‖H y‖ := hbound y (by simpa only [mem_sphere, dist_zero_right] using hy)
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hcy (pow_nonneg hr.le d))

/-- Trivial zero fiber makes a continuous homogeneous map of positive degree proper. -/
theorem isProperMap_of_homogeneous_zero_fiber {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : E → F) (hH : Continuous H) (d : ℕ) (hd : 0 < d)
    (hhom : ∀ (r : ℝ), 0 < r → ∀ x, H (r • x) = r ^ d • H x)
    (hzero : ∀ x, H x = 0 → x = 0) : IsProperMap H := by
  obtain ⟨c, hc, hbound⟩ := exists_homogeneous_norm_lower_bound H hH d hd hhom hzero
  refine isProperMap_iff_tendsto_cocompact.mpr ⟨hH, ?_⟩
  apply Filter.tendsto_cocompact_cocompact_of_norm
  intro A
  refine ⟨max 1 (A / c), ?_⟩
  intro x hx
  have hx1 : 1 ≤ ‖x‖ := (lt_of_le_of_lt (le_max_left _ _) hx).le
  have hxA : A / c < ‖x‖ := lt_of_le_of_lt (le_max_right _ _) hx
  have hAc : A < c * ‖x‖ := by
    have hh := (div_lt_iff₀ hc).mp hxA
    simpa only [mul_comm] using hh
  exact hAc.trans_le ((mul_le_mul_of_nonneg_left (le_self_pow₀ hx1 hd.ne') hc.le).trans (hbound x))

end GaloisForLFunctions.HTGeometry
