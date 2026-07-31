import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.PiL2
import GaloisForLFunctions.HTGeometry.NestedProjectionConvergence

/-!
# Uniform transport between nearby finite-dimensional subspaces

On a finite-dimensional domain, pointwise convergence of continuous linear maps is already
convergence in operator norm: an orthonormal basis turns the pointwise data into a uniform bound,
because every coordinate functional of an orthonormal basis has norm at most one.

The consequence used by nested-exhaustion boundary analysis is that a family of projections
converging strongly to a projection with finite-dimensional range converges uniformly on that
range.  In the deficiency-index-one case this immediately produces the transport unit vectors,
by normalizing the images of one fixed unit vector.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section FiniteDomain

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace 𝕜 N]

/-- **Operator norm from orthonormal coordinates.**  Every coordinate functional of an
orthonormal basis has norm at most one, so the operator norm is bounded by the sum of the norms of
the basis images. -/
theorem opNorm_le_sum_orthonormalBasis {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 N)
    (T : N →L[𝕜] E) : ‖T‖ ≤ ∑ j, ‖T (b j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound T (Finset.sum_nonneg fun j _ => norm_nonneg _) ?_
  intro x
  have hx : x = ∑ j, b.repr x j • b j := (b.sum_repr x).symm
  have hTx : T x = ∑ j, b.repr x j • T (b j) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [ContinuousLinearMap.map_smul]
  have hcoord : ∀ j, ‖b.repr x j‖ ≤ ‖x‖ := by
    intro j
    rw [b.repr_apply_apply]
    have := norm_inner_le_norm (𝕜 := 𝕜) (b j) x
    rw [b.orthonormal.1 j, one_mul] at this
    exact this
  calc ‖T x‖ = ‖∑ j, b.repr x j • T (b j)‖ := by rw [hTx]
    _ ≤ ∑ j, ‖b.repr x j • T (b j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖b.repr x j‖ * ‖T (b j)‖ := by
        exact Finset.sum_congr rfl fun j _ => norm_smul _ _
    _ ≤ ∑ j, ‖x‖ * ‖T (b j)‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right (hcoord j) (norm_nonneg _)
    _ = (∑ j, ‖T (b j)‖) * ‖x‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

variable [FiniteDimensional 𝕜 N]

/-- **Pointwise convergence on a finite-dimensional domain is uniform.** -/
theorem tendsto_opNorm_sub_of_tendsto_pointwise {ι : Type*} {l : Filter ι}
    (T : ι → N →L[𝕜] E) (T₀ : N →L[𝕜] E)
    (h : ∀ x : N, Tendsto (fun i => T i x) l (𝓝 (T₀ x))) :
    Tendsto (fun i => ‖T i - T₀‖) l (𝓝 0) := by
  classical
  set b := stdOrthonormalBasis 𝕜 N with hb
  have hsum : Tendsto (fun i => ∑ j, ‖(T i - T₀) (b j)‖) l (𝓝 0) := by
    have hzero : ((0 : ℝ)) = ∑ _j : Fin (Module.finrank 𝕜 N), (0 : ℝ) := by simp
    rw [hzero]
    refine tendsto_finsetSum _ fun j _ => ?_
    have hj : Tendsto (fun i => T i (b j) - T₀ (b j)) l (𝓝 0) := by
      have := (h (b j)).sub (tendsto_const_nhds (x := T₀ (b j)))
      simpa using this
    simpa using hj.norm
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hsum
  simpa using opNorm_le_sum_orthonormalBasis b (T i - T₀)

end FiniteDomain

section RankOne

/-- The transported unit vector: the normalized image of a unit vector under a projection. -/
noncomputable def lineTransport (F : E →L[𝕜] E) (e : E) : E := (((‖F e‖ : ℝ) : 𝕜))⁻¹ • F e

theorem norm_lineTransport {F : E →L[𝕜] E} {e : E} (h : F e ≠ 0) :
    ‖lineTransport F e‖ = 1 := by
  rw [lineTransport, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)

theorem lineTransport_mem_range {F : E →L[𝕜] E} {e : E} {K : Submodule 𝕜 E}
    (h : F e ∈ K) : lineTransport F e ∈ K := by
  rw [lineTransport]
  exact K.smul_mem _ h

/-- **Rank-one transport is automatic.**  If the projections converge strongly, the normalized
images of a fixed unit vector converge to it. -/
theorem tendsto_lineTransport {ι : Type*} {l : Filter ι} (F : ι → E →L[𝕜] E) {e : E}
    (he : ‖e‖ = 1) (h : Tendsto (fun i => F i e) l (𝓝 e)) :
    Tendsto (fun i => lineTransport (F i) e) l (𝓝 e) := by
  have hnorm : Tendsto (fun i => ‖F i e‖) l (𝓝 1) := by
    have := h.norm
    rwa [he] at this
  have hcast : Tendsto (fun i => ((‖F i e‖ : ℝ) : 𝕜)) l (𝓝 ((1 : ℝ) : 𝕜)) :=
    (RCLike.continuous_ofReal (K := 𝕜)).continuousAt.tendsto.comp hnorm
  have hinv : Tendsto (fun i => (((‖F i e‖ : ℝ) : 𝕜))⁻¹) l (𝓝 1) := by
    have h1 : ((1 : ℝ) : 𝕜) ≠ 0 := by simp
    have := hcast.inv₀ h1
    simpa using this
  have := hinv.smul h
  simpa [lineTransport] using this

/-- The rank-one operator `x ↦ ⟪e, x⟫ • u`. -/
noncomputable def rankOneTransport (e u : E) : E →L[𝕜] E :=
  (innerSL 𝕜 e).smulRight u

@[simp] theorem rankOneTransport_apply (e u x : E) :
    rankOneTransport (𝕜 := 𝕜) e u x = (inner 𝕜 e x : 𝕜) • u := rfl

/-- On a unit vector the rank-one transport is the orthogonal projection onto its line. -/
theorem rankOneTransport_self_eq_starProjection {e : E} (he : ‖e‖ = 1)
    [(𝕜 ∙ e).HasOrthogonalProjection] :
    rankOneTransport (𝕜 := 𝕜) e e = (𝕜 ∙ e).starProjection := by
  ext x
  rw [rankOneTransport_apply, starProjection_singleton, he]
  norm_num

/-- **Uniform transport in the rank-one case.**  Convergence of the transported unit vectors is
convergence of the transport operators in operator norm. -/
theorem tendsto_opNorm_rankOneTransport {ι : Type*} {l : Filter ι} (u : ι → E) (e : E)
    (h : Tendsto u l (𝓝 e)) :
    Tendsto (fun i => ‖rankOneTransport (𝕜 := 𝕜) e (u i)
      - rankOneTransport (𝕜 := 𝕜) e e‖) l (𝓝 0) := by
  have hsub : ∀ i, rankOneTransport (𝕜 := 𝕜) e (u i) - rankOneTransport (𝕜 := 𝕜) e e
      = (innerSL 𝕜 e).smulRight (u i - e) := by
    intro i
    ext x
    simp [rankOneTransport, smul_sub]
  have hbound : ∀ i, ‖rankOneTransport (𝕜 := 𝕜) e (u i)
      - rankOneTransport (𝕜 := 𝕜) e e‖ ≤ ‖e‖ * ‖u i - e‖ := by
    intro i
    rw [hsub i]
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hzero : Tendsto (fun i => ‖e‖ * ‖u i - e‖) l (𝓝 0) := by
    have : Tendsto (fun i => ‖u i - e‖) l (𝓝 0) := by
      simpa using (h.sub (tendsto_const_nhds (x := e))).norm
    simpa using this.const_mul ‖e‖
  exact squeeze_zero (fun i => norm_nonneg _) hbound hzero

end RankOne

/-! ## Deficiency transport of a nested exhaustion at index one -/

/-- **Automatic boundary transport at deficiency index one.**  For a nested exhaustion whose
global deficiency space is the line through a unit vector `e`, the normalized images of `e` under
the stagewise deficiency projections converge to `e`, and the associated rank-one transports
converge to the global deficiency projection in operator norm. -/
theorem tendsto_opNorm_deficiency_rankOneTransport
    {ι : Type*} [Preorder ι] (HS M : ι → Submodule 𝕜 E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdense : (⨆ i, HS i).topologicalClosure = ⊤)
    {e : E} (he : ‖e‖ = 1) [(𝕜 ∙ e).HasOrthogonalProjection]
    (hline : ((⨆ i, M i).topologicalClosure)ᗮ = 𝕜 ∙ e) :
    Tendsto (fun i => ‖rankOneTransport (𝕜 := 𝕜) e
        (lineTransport ((HS i ⊓ (M i)ᗮ).starProjection) e)
      - (𝕜 ∙ e).starProjection‖) atTop (𝓝 0) := by
  have hpt : Tendsto (fun i => (HS i ⊓ (M i)ᗮ).starProjection e) atTop
      (𝓝 (((⨆ i, M i).topologicalClosure)ᗮ.starProjection e)) :=
    tendsto_deficiency_starProjection HS M hHS hM hle hdense e
  have hlim : ((⨆ i, M i).topologicalClosure)ᗮ.starProjection e = e := by
    rw [starProjection_eq_self_iff, hline]
    exact Submodule.mem_span_singleton_self e
  rw [hlim] at hpt
  have hu := tendsto_lineTransport (𝕜 := 𝕜) (fun i => (HS i ⊓ (M i)ᗮ).starProjection) he hpt
  have hop := tendsto_opNorm_rankOneTransport (𝕜 := 𝕜)
    (fun i => lineTransport ((HS i ⊓ (M i)ᗮ).starProjection) e) e hu
  rwa [rankOneTransport_self_eq_starProjection he] at hop

end GaloisForLFunctions.HTGeometry
