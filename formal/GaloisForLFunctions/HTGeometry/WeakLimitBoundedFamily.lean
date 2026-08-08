import Mathlib

/-!
# Weak limits of norm-bounded families

A family bounded in a Hilbert space whose inner products converge against a dense subspace has a
weak limit in the space, of no larger norm.  This is the passage a mollifier argument needs: the
mollified profiles are uniformly bounded by a coercive energy estimate and converge against test
functions, and the conclusion is that the *unmollified* object is in the space rather than merely a
distribution.

No weak compactness is used.  The uniform bound upgrades convergence on a dense subspace to
convergence everywhere, the limit functional is then bounded on the whole space by the same
constant, and Riesz representation produces the limit.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A uniform bound upgrades dense convergence to convergence everywhere.** -/
theorem cauchySeq_inner_of_bounded {u : ℕ → H} {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M)
    {p : Submodule 𝕜 H} (hp : Dense (p : Set H))
    (hconv : ∀ φ ∈ p, ∃ c : 𝕜, Tendsto (fun n => (inner 𝕜 (u n) φ : 𝕜)) atTop (𝓝 c))
    (φ : H) : CauchySeq (fun n => (inner 𝕜 (u n) φ : 𝕜)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨ψ, hψp, hψ⟩ : ∃ ψ ∈ (p : Set H), dist φ ψ < ε / (3 * (M + 1)) := by
    have hpos : 0 < ε / (3 * (M + 1)) := by positivity
    obtain ⟨ψ, hψp, hψ⟩ := Metric.mem_closure_iff.mp (hp.closure_eq ▸ Set.mem_univ φ) _ hpos
    exact ⟨ψ, hψp, hψ⟩
  obtain ⟨c, hc⟩ := hconv ψ hψp
  have hcauchy : CauchySeq (fun n => (inner 𝕜 (u n) ψ : 𝕜)) := hc.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (ε / 3) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hsplit : ∀ k : ℕ, dist (inner 𝕜 (u k) φ : 𝕜) (inner 𝕜 (u k) ψ : 𝕜) < ε / 3 := by
    intro k
    have hd : (inner 𝕜 (u k) φ : 𝕜) - (inner 𝕜 (u k) ψ : 𝕜) = inner 𝕜 (u k) (φ - ψ) := by
      rw [inner_sub_right]
    rw [dist_eq_norm, hd]
    calc ‖(inner 𝕜 (u k) (φ - ψ) : 𝕜)‖ ≤ ‖u k‖ * ‖φ - ψ‖ := norm_inner_le_norm _ _
      _ ≤ M * ‖φ - ψ‖ := by
          refine mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _)
      _ < ε / 3 := by
          have hnorm : ‖φ - ψ‖ < ε / (3 * (M + 1)) := by rwa [← dist_eq_norm]
          have hMlt : M * ‖φ - ψ‖ ≤ (M + 1) * ‖φ - ψ‖ := by nlinarith [norm_nonneg (φ - ψ)]
          have : (M + 1) * ‖φ - ψ‖ < (M + 1) * (ε / (3 * (M + 1))) := by
            refine mul_lt_mul_of_pos_left hnorm (by linarith)
          have heq : (M + 1) * (ε / (3 * (M + 1))) = ε / 3 := by
            field_simp
          linarith [heq ▸ this]
  calc dist (inner 𝕜 (u m) φ : 𝕜) (inner 𝕜 (u n) φ : 𝕜)
      ≤ dist (inner 𝕜 (u m) φ : 𝕜) (inner 𝕜 (u m) ψ : 𝕜)
        + dist (inner 𝕜 (u m) ψ : 𝕜) (inner 𝕜 (u n) φ : 𝕜) := dist_triangle _ _ _
    _ ≤ dist (inner 𝕜 (u m) φ : 𝕜) (inner 𝕜 (u m) ψ : 𝕜)
        + (dist (inner 𝕜 (u m) ψ : 𝕜) (inner 𝕜 (u n) ψ : 𝕜)
          + dist (inner 𝕜 (u n) ψ : 𝕜) (inner 𝕜 (u n) φ : 𝕜)) := by
        gcongr
        exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
        have h1 := hsplit m
        have h2 := hN m hm n hn
        have h3 : dist (inner 𝕜 (u n) ψ : 𝕜) (inner 𝕜 (u n) φ : 𝕜) < ε / 3 := by
          rw [dist_comm]; exact hsplit n
        linarith
    _ = ε := by ring

/-- **The weak limit exists.**  A family bounded by `M` whose inner products converge against a
dense subspace converges weakly to a vector of norm at most `M`. -/
theorem exists_weakLimit_of_bounded {u : ℕ → H} {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M)
    {p : Submodule 𝕜 H} (hp : Dense (p : Set H))
    (hconv : ∀ φ ∈ p, ∃ c : 𝕜, Tendsto (fun n => (inner 𝕜 (u n) φ : 𝕜)) atTop (𝓝 c)) :
    ∃ w : H, ‖w‖ ≤ M ∧
      ∀ φ : H, Tendsto (fun n => (inner 𝕜 (u n) φ : 𝕜)) atTop (𝓝 (inner 𝕜 w φ)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  -- the limit functional
  have hex : ∀ φ : H, ∃ c : 𝕜, Tendsto (fun n => (inner 𝕜 (u n) φ : 𝕜)) atTop (𝓝 c) := by
    intro φ
    exact cauchySeq_tendsto_of_complete (cauchySeq_inner_of_bounded hM hp hconv φ)
  choose Λ hΛ using hex
  have hadd : ∀ φ ψ : H, Λ (φ + ψ) = Λ φ + Λ ψ := by
    intro φ ψ
    refine tendsto_nhds_unique (hΛ (φ + ψ)) ?_
    have := (hΛ φ).add (hΛ ψ)
    refine this.congr fun n => ?_
    rw [inner_add_right]
  have hsmul : ∀ (c : 𝕜) (φ : H), Λ (c • φ) = c * Λ φ := by
    intro c φ
    refine tendsto_nhds_unique (hΛ (c • φ)) ?_
    have := (hΛ φ).const_mul c
    refine this.congr fun n => ?_
    rw [inner_smul_right]
  have hbound : ∀ φ : H, ‖Λ φ‖ ≤ M * ‖φ‖ := by
    intro φ
    refine le_of_tendsto (hΛ φ).norm (Eventually.of_forall fun n => ?_)
    calc ‖(inner 𝕜 (u n) φ : 𝕜)‖ ≤ ‖u n‖ * ‖φ‖ := norm_inner_le_norm _ _
      _ ≤ M * ‖φ‖ := mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _)
  let Λlin : H →ₗ[𝕜] 𝕜 :=
    { toFun := Λ
      map_add' := hadd
      map_smul' := by intro c φ; simpa using hsmul c φ }
  let Λcont : H →L[𝕜] 𝕜 := Λlin.mkContinuous M hbound
  refine ⟨(InnerProductSpace.toDual 𝕜 H).symm Λcont, ?_, ?_⟩
  · have hnorm : ‖(InnerProductSpace.toDual 𝕜 H).symm Λcont‖ = ‖Λcont‖ :=
      (InnerProductSpace.toDual 𝕜 H).symm.norm_map Λcont
    rw [hnorm]
    exact Λlin.mkContinuous_norm_le hM0 hbound
  · intro φ
    have hval : (inner 𝕜 ((InnerProductSpace.toDual 𝕜 H).symm Λcont) φ : 𝕜) = Λ φ := by
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    rw [hval]
    exact hΛ φ

end GaloisForLFunctions.HTGeometry
