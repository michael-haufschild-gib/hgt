import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Deficiency projections of a nested exhaustion

A nested exhaustion of Hilbert spaces carries two monotone families of closed subspaces: the
ambient spaces `H_a`, whose closed span is everything, and the ranges `M_a` of the shifted
symmetric operators, whose closed span is the global range `M`.  The deficiency space at stage `a`
is the part of `H_a` orthogonal to `M_a`.

Two facts drive the whole boundary-phase analysis of such an exhaustion.  First, for nested closed
subspaces the projection onto the relative complement is the plain difference of the two
projections.  Second, monotone families of projections converge strongly to the projection onto
the closed span.  Together they make the deficiency projections converge strongly to the
projection onto the global deficiency space — with no hypothesis beyond nesting and density.

Nothing here mentions unbounded operators: the statements are about closed subspaces, which is
exactly the level at which the Cayley picture of a symmetric operator lives.
-/

namespace GaloisForLFunctions.HTGeometry

open Submodule Filter Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Relative complement of nested closed subspaces.**  If `M ≤ K`, the projection onto the part
of `K` orthogonal to `M` is the difference of the two projections. -/
theorem starProjection_inf_orthogonal_apply {M K : Submodule 𝕜 E}
    [M.HasOrthogonalProjection] [K.HasOrthogonalProjection]
    [(K ⊓ Mᗮ).HasOrthogonalProjection] (hMK : M ≤ K) (x : E) :
    (K ⊓ Mᗮ).starProjection x = K.starProjection x - M.starProjection x := by
  refine eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ (K.starProjection_apply_mem x)
      (hMK (M.starProjection_apply_mem x)), ?_⟩
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hK : inner 𝕜 (x - K.starProjection x) v = 0 :=
      K.starProjection_inner_eq_zero x v (hMK hv)
    have hM : inner 𝕜 (x - M.starProjection x) v = 0 :=
      M.starProjection_inner_eq_zero x v hv
    have hKv : inner 𝕜 (K.starProjection x) v = inner 𝕜 x v := by
      rw [inner_sub_left] at hK
      linear_combination -hK
    have hMv : inner 𝕜 (M.starProjection x) v = inner 𝕜 x v := by
      rw [inner_sub_left] at hM
      linear_combination -hM
    have : inner 𝕜 (K.starProjection x - M.starProjection x) v = 0 := by
      rw [inner_sub_left, hKv, hMv, sub_self]
    rw [inner_eq_zero_symm]
    exact this
  · intro w hw
    have hwK : w ∈ K := (Submodule.mem_inf.mp hw).1
    have hwM : w ∈ Mᗮ := (Submodule.mem_inf.mp hw).2
    have h1 : inner 𝕜 (x - K.starProjection x) w = 0 :=
      K.starProjection_inner_eq_zero x w hwK
    have h2 : inner 𝕜 (M.starProjection x) w = 0 :=
      (Submodule.mem_orthogonal _ _).mp hwM _ (M.starProjection_apply_mem x)
    have hrw : x - (K.starProjection x - M.starProjection x)
        = (x - K.starProjection x) + M.starProjection x := by abel
    rw [hrw, inner_add_left, h1, h2, add_zero]

/-- Operator form of the relative-complement identity. -/
theorem starProjection_inf_orthogonal {M K : Submodule 𝕜 E}
    [M.HasOrthogonalProjection] [K.HasOrthogonalProjection]
    [(K ⊓ Mᗮ).HasOrthogonalProjection] (hMK : M ≤ K) :
    (K ⊓ Mᗮ).starProjection = K.starProjection - M.starProjection := by
  ext x
  simpa using starProjection_inf_orthogonal_apply hMK x

variable {ι : Type*} [Preorder ι]

/-- **Deficiency projections of a nested exhaustion converge.**  If the ambient spaces exhaust the
whole space and the ranges exhaust their closed span, then the projections onto the stagewise
deficiency spaces converge strongly to the projection onto the global deficiency space. -/
theorem tendsto_deficiency_starProjection
    (HS M : ι → Submodule 𝕜 E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdense : (⨆ i, HS i).topologicalClosure = ⊤) (x : E) :
    Tendsto (fun i => (HS i ⊓ (M i)ᗮ).starProjection x) atTop
      (𝓝 (((⨆ i, M i).topologicalClosure)ᗮ.starProjection x)) := by
  have h1 := starProjection_tendsto_closure_iSup HS hHS x
  have h2 := starProjection_tendsto_closure_iSup M hM x
  have htop : (⨆ i, HS i).topologicalClosure.starProjection x = x := by
    rw [starProjection_eq_self_iff, hdense]
    trivial
  rw [htop] at h1
  have hsub := h1.sub h2
  have hlimit : x - (⨆ i, M i).topologicalClosure.starProjection x
      = ((⨆ i, M i).topologicalClosure)ᗮ.starProjection x := by
    rw [starProjection_orthogonal]
    simp
  rw [hlimit] at hsub
  refine hsub.congr fun i => ?_
  exact (starProjection_inf_orthogonal_apply (hle i) x).symm

end GaloisForLFunctions.HTGeometry
