import GaloisForLFunctions.HTGeometry.NestedExhaustionCayleyLimit

/-!
# Phase universality when the global deficiency vanishes

For a nested symmetric-operator exhaustion, every finite Cayley transform is the sum of a base
partial isometry on the shifted range and a contractive boundary block on the finite deficiency
space.  If the shifted ranges exhaust the whole ambient Hilbert space, finite deficiency
projections converge strongly to zero.  The moving boundary blocks then disappear strongly with
no convergence assumption on their phases.

This is the rank-drop counterpart of boundary-phase locking.  Stable nonzero global deficiency
requires convergence of finite boundary blocks; zero global deficiency makes every uniformly
contractive boundary schedule asymptotically equivalent.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} {l : Filter ι}

/-- If finite deficiency projections vanish strongly, every uniformly contractive moving boundary
block disappears from the assembled Cayley transform.  No convergence of the boundary blocks is
required. -/
theorem tendsto_cayleyAssembly_of_deficiency_vanishes
    (V : E →L[𝕜] E) {Q Eb W : ι → E →L[𝕜] E}
    (hQ : ∀ x, Tendsto (fun i => Q i x) l (𝓝 x))
    (hE : ∀ x, Tendsto (fun i => Eb i x) l (𝓝 0))
    (hW : ∀ i, ‖W i‖ ≤ 1) (x : E) :
    Tendsto (fun i => cayleyAssembly V (W i) (Q i) (Eb i) x) l (𝓝 (V x)) := by
  have hbase : Tendsto (fun i => V (Q i x)) l (𝓝 (V x)) :=
    (V.continuous.continuousAt.tendsto).comp (hQ x)
  have hboundary : Tendsto (fun i => W i (Eb i x)) l (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hnorm : Tendsto (fun i => ‖Eb i x‖) l (𝓝 0) := by
      simpa using (hE x).norm
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hnorm
    exact le_trans (ContinuousLinearMap.le_opNorm (W i) (Eb i x))
      (by simpa using mul_le_mul_of_nonneg_right (hW i) (norm_nonneg (Eb i x)))
  simpa [cayleyAssembly_apply] using hbase.add hboundary

/-- Dense nested shifted ranges force finite deficiency projections to vanish strongly. -/
theorem tendsto_deficiency_starProjection_zero
    {ι : Type*} [Preorder ι]
    (HS M : ι → Submodule 𝕜 E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdenseHS : (⨆ i, HS i).topologicalClosure = ⊤)
    (hdenseM : (⨆ i, M i).topologicalClosure = ⊤) (x : E) :
    Tendsto (fun i => (HS i ⊓ (M i)ᗮ).starProjection x) atTop (𝓝 0) := by
  have h := tendsto_deficiency_starProjection HS M hHS hM hle hdenseHS x
  simpa [hdenseM] using h

/-- **Phase universality for a dense nested range exhaustion.**  Once the finite shifted ranges
exhaust the whole Hilbert space, every contractive boundary schedule has the same strong Cayley
limit, namely the global unitary base map `V`. -/
theorem tendsto_cayleyAssembly_of_dense_nested_ranges
    {ι : Type*} [Preorder ι]
    (HS M : ι → Submodule 𝕜 E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdenseHS : (⨆ i, HS i).topologicalClosure = ⊤)
    (hdenseM : (⨆ i, M i).topologicalClosure = ⊤)
    (V : E →L[𝕜] E) {W : ι → E →L[𝕜] E} (hW : ∀ i, ‖W i‖ ≤ 1) (x : E) :
    Tendsto (fun i => cayleyAssembly V (W i) (M i).starProjection
      (HS i ⊓ (M i)ᗮ).starProjection x) atTop (𝓝 (V x)) := by
  have hQ : ∀ y : E, Tendsto (fun i => (M i).starProjection y) atTop (𝓝 y) := by
    intro y
    have h := starProjection_tendsto_closure_iSup M hM y
    have hlim : (⨆ i, M i).topologicalClosure.starProjection y = y := by
      rw [starProjection_eq_self_iff, hdenseM]
      trivial
    rw [hlim] at h
    exact h
  have hE : ∀ y : E,
      Tendsto (fun i => (HS i ⊓ (M i)ᗮ).starProjection y) atTop (𝓝 0) :=
    fun y => tendsto_deficiency_starProjection_zero HS M hHS hM hle hdenseHS hdenseM y
  exact tendsto_cayleyAssembly_of_deficiency_vanishes V hQ hE hW x

/-- The phase-universal Cayley limit transfers to the generalized strong resolvent topology. -/
theorem tendsto_cayleyResolvent_of_dense_nested_ranges
    {ι : Type*} [Preorder ι]
    (HS M : ι → Submodule 𝕜 E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdenseHS : (⨆ i, HS i).topologicalClosure = ⊤)
    (hdenseM : (⨆ i, M i).topologicalClosure = ⊤)
    (V : E →L[𝕜] E) {W : ι → E →L[𝕜] E} (hW : ∀ i, ‖W i‖ ≤ 1)
    (c : 𝕜) (x : E) :
    Tendsto (fun i => (c • ((HS i).starProjection -
      cayleyAssembly V (W i) (M i).starProjection
        (HS i ⊓ (M i)ᗮ).starProjection)) x) atTop
      (𝓝 (cayleyResolvent c V x)) := by
  have hP : ∀ y : E, Tendsto (fun i => (HS i).starProjection y) atTop (𝓝 y) := by
    intro y
    have h := starProjection_tendsto_closure_iSup HS hHS y
    have hlim : (⨆ i, HS i).topologicalClosure.starProjection y = y := by
      rw [starProjection_eq_self_iff, hdenseHS]
      trivial
    rw [hlim] at h
    exact h
  have hC : ∀ y : E, Tendsto (fun i => cayleyAssembly V (W i) (M i).starProjection
      (HS i ⊓ (M i)ᗮ).starProjection y) atTop (𝓝 (V y)) :=
    fun y => tendsto_cayleyAssembly_of_dense_nested_ranges HS M hHS hM hle
      hdenseHS hdenseM V hW y
  exact tendsto_cayleyResolvent c hP hC x

end GaloisForLFunctions.HTGeometry
