import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import GaloisForLFunctions.RHTower.ApproximationNumberLowerBound

/-!
# An algebra of finite-rank operators

The approximation-number layer defines "rank at most `n`" but produced only the zero operator with
that property, so the upper bound `a_n ≤ ‖T − F‖` had nothing to be applied to.

The finite-rank operators form the expected ideal: composing on either side keeps the rank, as do
scalar multiples and negation, and the orthogonal projection onto a finite-dimensional subspace has
rank its dimension.  Together with the subspace lower bound this closes the sandwich: an
approximation number is pinned by one projection and one expanded subspace.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Post-composition preserves finite rank. -/
theorem HasRankLE.comp_left {F : H →L[ℂ] H} {n : ℕ} (hF : HasRankLE F n) (T : H →L[ℂ] H) :
    HasRankLE (T.comp F) n := by
  obtain ⟨V, hVfd, hVle, hVmem⟩ := hF
  refine ⟨Submodule.map (T : H →ₗ[ℂ] H) V, ?_, ?_, ?_⟩
  · exact Module.Finite.map _ _
  · exact le_trans (Submodule.finrank_map_le _ _) hVle
  · intro x
    exact Submodule.mem_map_of_mem (hVmem x)

/-- Pre-composition preserves finite rank. -/
theorem HasRankLE.comp_right {F : H →L[ℂ] H} {n : ℕ} (hF : HasRankLE F n) (T : H →L[ℂ] H) :
    HasRankLE (F.comp T) n := by
  obtain ⟨V, hVfd, hVle, hVmem⟩ := hF
  exact ⟨V, hVfd, hVle, fun x => hVmem (T x)⟩

/-- Scalar multiples preserve finite rank. -/
theorem HasRankLE.smul {F : H →L[ℂ] H} {n : ℕ} (hF : HasRankLE F n) (c : ℂ) :
    HasRankLE (c • F) n := by
  obtain ⟨V, hVfd, hVle, hVmem⟩ := hF
  exact ⟨V, hVfd, hVle, fun x => V.smul_mem c (hVmem x)⟩

theorem HasRankLE.neg {F : H →L[ℂ] H} {n : ℕ} (hF : HasRankLE F n) :
    HasRankLE (-F) n := by
  obtain ⟨V, hVfd, hVle, hVmem⟩ := hF
  exact ⟨V, hVfd, hVle, fun x => V.neg_mem (hVmem x)⟩

/-- The orthogonal projection onto a finite-dimensional subspace has rank its dimension. -/
theorem hasRankLE_starProjection (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    [W.HasOrthogonalProjection] {n : ℕ} (hW : Module.finrank ℂ W ≤ n) :
    HasRankLE W.starProjection n :=
  ⟨W, inferInstance, hW, fun x => (W.orthogonalProjectionOnto x).2⟩

/-- **The two-sided pin.**  A projection realizing the distance and an expanded subspace of one
higher dimension determine the approximation number exactly. -/
theorem approxNumber_eq_of_projection
    {T : H →L[ℂ] H} {n : ℕ} {c : ℝ}
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] [V.HasOrthogonalProjection]
    (hVle : Module.finrank ℂ V ≤ n)
    (hdist : ‖T - V.starProjection‖ = c)
    (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hdim : n + 1 ≤ Module.finrank ℂ W)
    (hlb : ∀ w ∈ W, c * ‖w‖ ≤ ‖T w‖) :
    approxNumber T n = c :=
  approxNumber_eq_of_subspace_of_hasRankLE W hdim hlb _
    (hasRankLE_starProjection V hVle) hdist

end RHTower

end
