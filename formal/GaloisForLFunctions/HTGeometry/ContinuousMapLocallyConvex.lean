import GaloisForLFunctions.HTGeometry.HolomorphicSubalgebra
import Mathlib.Analysis.LocallyConvex.Basic

/-!
# The compact-open topology on complex-valued continuous maps is locally convex

Uniform convergence on compact sets is a locally convex topology: a neighbourhood basis of the
origin consists of the sets `{f : ∀ x ∈ K, ‖f x‖ < ε}` with `K` compact and `ε` positive, and each
of those is convex because the norm is.

No hypothesis on the domain is needed.  This makes every space of continuous complex-valued
functions — in particular the Fréchet spaces of holomorphic functions on an open set, carried as
subspaces of `C(X, ℂ)` — a legitimate input to the Hahn–Banach separation arguments.

* `HTGeometry.hasBasis_nhds_zero_continuousMap`;
* the instance `LocallyConvexSpace ℝ C(X, ℂ)`.
-/

open Filter Metric
open scoped Topology

namespace HTGeometry

variable {X : Type*} [TopologicalSpace X]

/-- **The compact-open neighbourhood basis of the origin.** -/
theorem hasBasis_nhds_zero_continuousMap :
    (𝓝 (0 : C(X, ℂ))).HasBasis (fun p : Set X × ℝ => IsCompact p.1 ∧ 0 < p.2)
      (fun p => {f : C(X, ℂ) | ∀ x ∈ p.1, ‖f x‖ < p.2}) := by
  have hbu := Filter.HasBasis.compactConvergenceUniformity
    (α := X) (β := ℂ) Metric.uniformity_basis_dist
  have hb := nhds_basis_uniformity' (x := (0 : C(X, ℂ))) hbu
  refine hb.to_hasBasis ?_ ?_
  · rintro ⟨K, ε⟩ ⟨hK, hε⟩
    refine ⟨⟨K, ε⟩, ⟨hK, hε⟩, fun f hf x hx => ?_⟩
    have := hf x hx
    simpa [Complex.dist_eq] using this
  · rintro ⟨K, ε⟩ ⟨hK, hε⟩
    refine ⟨⟨K, ε⟩, ⟨hK, hε⟩, fun f hf x hx => ?_⟩
    have := hf x hx
    simpa [Complex.dist_eq] using this

/-- **Each basic compact-open neighbourhood of the origin is convex.** -/
theorem convex_nhds_zero_continuousMap (K : Set X) (ε : ℝ) :
    Convex ℝ {f : C(X, ℂ) | ∀ x ∈ K, ‖f x‖ < ε} := by
  intro f hf g hg a b ha hb hab x hx
  have hfx : ‖f x‖ < ε := hf x hx
  have hgx : ‖g x‖ < ε := hg x hx
  have hval : ‖(a • f + b • g) x‖ ≤ a * ‖f x‖ + b * ‖g x‖ := by
    have hsplit : (a • f + b • g) x = a • f x + b • g x := by simp
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul]
    simp [Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  refine lt_of_le_of_lt hval ?_
  have hsum : a * ε + b * ε = ε := by
    rw [← add_mul, hab, one_mul]
  rcases ha.eq_or_lt with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    rw [← ha0, hb1]
    simpa using hgx
  · have h1 : a * ‖f x‖ < a * ε := mul_lt_mul_of_pos_left hfx ha0
    have h2 : b * ‖g x‖ ≤ b * ε := mul_le_mul_of_nonneg_left hgx.le hb
    linarith

instance instLocallyConvexSpaceContinuousMap : LocallyConvexSpace ℝ C(X, ℂ) :=
  LocallyConvexSpace.ofBasisZero ℝ C(X, ℂ) _ _ hasBasis_nhds_zero_continuousMap
    fun p _ => convex_nhds_zero_continuousMap p.1 p.2

end HTGeometry
