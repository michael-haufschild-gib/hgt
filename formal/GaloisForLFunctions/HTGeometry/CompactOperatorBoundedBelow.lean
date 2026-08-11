import Mathlib

/-!
# A compact operator cannot be bounded below on an infinite-dimensional subspace

If a compact operator is bounded below on a closed subspace, that subspace is finite dimensional.
The closed unit ball of the subspace is the preimage, under the antilipschitz restriction of the
operator, of a totally bounded set, hence totally bounded; completeness turns it into a compact
neighbourhood of the origin, and a locally compact normed space over a nontrivially normed
complete field is finite dimensional.

This is the mechanism behind finiteness of spectral projections for a flow whose smoothings are
compact: on a spectral interval where the smoothing symbol is bounded away from zero, the
smoothing operator is bounded below, so the spectral subspace is finite dimensional.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀]

omit [CompleteSpace E] in
/-- The closed unit ball of a closed subspace on which a compact operator is bounded below is
totally bounded. -/
theorem totallyBounded_closedBall_of_isCompactOperator_of_bounded_below
    {K : E →L[𝕜] F₀} (hK : IsCompactOperator K)
    (S : Submodule 𝕜 E) {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ x ∈ S, c * ‖x‖ ≤ ‖K x‖) :
    TotallyBounded (Metric.closedBall (0 : S) 1) := by
  classical
  -- the restriction of `K` to `S` is antilipschitz
  set f : S → F₀ := fun x => K (x : E) with hf
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) f := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    have hmem : ((x : E) - (y : E)) ∈ S := S.sub_mem x.2 y.2
    have h := hbdd _ hmem
    have hdist : dist (f x) (f y) = ‖K ((x : E) - (y : E))‖ := by
      rw [hf]
      simp [dist_eq_norm, ← map_sub]
    have hdistS : dist x y = ‖(x : E) - (y : E)‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
    rw [hdist, hdistS, Real.coe_toNNReal _ (by positivity), inv_mul_eq_div, le_div_iff₀ hc]
    linarith [h]
  have hfc : UniformContinuous f :=
    (K.lipschitz.comp (LipschitzWith.subtype_val _)).uniformContinuous
  have hind : IsUniformInducing f := hanti.isUniformInducing hfc
  -- the image of the ambient closed unit ball has compact closure
  have hcpt := hK.isCompact_closure_image_closedBall 1
  have hTB := hcpt.totallyBounded
  have hpre := totallyBounded_preimage hind hTB
  refine hpre.subset ?_
  intro x hx
  have hx1 : ‖(x : E)‖ ≤ 1 := by
    have := mem_closedBall.mp hx
    simpa [dist_eq_norm] using this
  exact subset_closure ⟨(x : E), by simpa [dist_eq_norm] using hx1, rfl⟩

/-- **A compact operator bounded below on a closed subspace forces finite dimension.** -/
theorem finiteDimensional_of_isCompactOperator_of_bounded_below
    {K : E →L[𝕜] F₀} (hK : IsCompactOperator K)
    (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E)) {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ x ∈ S, c * ‖x‖ ≤ ‖K x‖) :
    FiniteDimensional 𝕜 S := by
  haveI : CompleteSpace S := hS.completeSpace_coe
  have hTB : TotallyBounded (Metric.closedBall (0 : S) 1) :=
    totallyBounded_closedBall_of_isCompactOperator_of_bounded_below hK S hc hbdd
  have hcpt : IsCompact (Metric.closedBall (0 : S) 1) :=
    hTB.isCompact_of_isClosed Metric.isClosed_closedBall
  refine FiniteDimensional.of_isCompactOperator_id ?_
  refine (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).2 ?_
  refine ⟨Metric.closedBall (0 : S) 1, Metric.closedBall_mem_nhds _ one_pos, ?_⟩
  simpa [Set.image_id, IsClosed.closure_eq Metric.isClosed_closedBall] using hcpt

/-! ## Eigenvalue separation -/

section InnerProduct

variable {𝕜' : Type*} [RCLike 𝕜'] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace 𝕜' F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- **A compact operator has only finitely many orthonormal eigenvectors whose eigenvalues are
bounded away from zero.**  Their images are pairwise `ε`-separated inside a compact set, so no
subsequence can converge.  This is finiteness of multiplicities together with the absence of a
finite accumulation point of the eigenvalues away from the origin. -/
theorem finite_of_orthonormal_eigenvectors_of_le_norm
    {K : F →L[𝕜'] F} (hK : IsCompactOperator K) {ι : Type*} {e : ι → F}
    (he : Orthonormal 𝕜' e) {lam : ι → 𝕜'} (heig : ∀ i, K (e i) = lam i • e i)
    {ε : ℝ} (hε : 0 < ε) (hlam : ∀ i, ε ≤ ‖lam i‖) :
    Finite ι := by
  classical
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  set g : ℕ ↪ ι := Infinite.natEmbedding ι with hg
  have hmem : ∀ n : ℕ, K (e (g n)) ∈ closure (K '' Metric.closedBall (0 : F) 1) := by
    intro n
    refine subset_closure ⟨e (g n), ?_, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_eq (he.1 (g n))
  have hsep : ∀ m n : ℕ, m ≠ n → ε ≤ dist (K (e (g m))) (K (e (g n))) := by
    intro m n hmn
    have hne : g m ≠ g n := fun h => hmn (g.injective h)
    have hself : inner 𝕜' (e (g m)) (e (g m)) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he.1 (g m)]
      norm_num
    have hinner :
        inner 𝕜' (e (g m)) (K (e (g m)) - K (e (g n))) = lam (g m) := by
      rw [heig, heig, inner_sub_right, inner_smul_right, inner_smul_right,
        he.2 hne, hself]
      ring
    have hcs := norm_inner_le_norm (𝕜 := 𝕜') (e (g m)) (K (e (g m)) - K (e (g n)))
    rw [hinner, he.1 (g m), one_mul] at hcs
    rw [dist_eq_norm]
    exact le_trans (hlam (g m)) hcs
  obtain ⟨a, -, φ, hφ, hconv⟩ :=
    (hK.isCompact_closure_image_closedBall 1).tendsto_subseq hmem
  have hcauchy := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hlt := hN (N + 1) (Nat.le_succ N) N le_rfl
  have hne : φ (N + 1) ≠ φ N := fun h => by
    have := hφ.injective h
    omega
  exact absurd hlt (not_lt.mpr (hsep _ _ hne))

end InnerProduct

end GaloisForLFunctions.HTGeometry
