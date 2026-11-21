import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Dimension of the levels shared by two distance functions -/
open Set MeasureTheory
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnLevels
noncomputable section

/-- If one distance at t is bounded by the other at u plus a power of
the lag, the values at their coincidence times have dimension at most
the reciprocal power. The same estimate in the opposite time direction
gives the Hölder bound on that set. -/
theorem shared_levels_dimension (f g : ℝ → ℝ) (K : ℝ≥0) (p : ℕ) (hp : 0 < p)
    (h : ∀ t u, g t ≤ f u + (K:ℝ)*|t-u|^p) :
    dimH (f '' {t | f t=g t}) ≤ 1/(p:ℝ≥0∞) := by
  let S := {t | f t=g t}
  have hh : HolderOnWith K (p:ℝ≥0) f S := by
    intro t ht u hu
    have ht' : f t=g t := ht
    have hu' : f u=g u := hu
    have h1 := h t u
    have h2 := h u t
    rw [←ht'] at h1
    rw [←hu',abs_sub_comm u t] at h2
    have hd : dist (f t) (f u) ≤ (K:ℝ)*dist t u^p := by
      rw [Real.dist_eq,Real.dist_eq,abs_le]
      constructor <;> linarith only [h1,h2]
    have hn : nndist (f t) (f u) ≤ K*nndist t u^p := by
      rw [←NNReal.coe_le_coe,NNReal.coe_mul,NNReal.coe_pow]
      exact hd
    simpa only [edist_nndist,NNReal.coe_natCast,ENNReal.rpow_natCast,←ENNReal.coe_pow,
      ←ENNReal.coe_mul,ENNReal.coe_le_coe] using hn
  have hS := (dimH_mono (subset_univ S)).trans_eq Real.dimH_univ
  exact (hh.dimH_image_le (Nat.cast_pos.mpr hp)).trans (by
    simpa only [ENNReal.coe_natCast] using div_le_div_right' hS (p:ℝ≥0∞))

#print axioms shared_levels_dimension
end
end GaloisForLFunctions.HTGeometry.ReturnLevels
