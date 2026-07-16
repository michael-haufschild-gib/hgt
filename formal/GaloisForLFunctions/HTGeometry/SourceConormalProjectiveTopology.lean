import GaloisForLFunctions.HTGeometry.ClockDescentAnomaly

/-!
# The source-conormal clock topology is projective

The minimal clock-topology refinement forced by a nonzero source conormal remembers its line,
but not its normalization.  Multiplying the conormal by a nonzero complex scalar gives exactly
the same induced topology, while its squared response norm is multiplied by the squared norm of
that scalar.

Thus topology can locate a hypertranscendental conormal in the finite-observable corona, but it
cannot select a numerical capacity such as the four-unit Möbius--Gamma normalization.  That scale
is genuinely additional Hermitian source data.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pulling a normed complex target topology back along a linear functional depends only on the
projective line of a nonzero scalar multiple of that functional. -/
theorem induced_smul_linearMap_eq
    {V Q : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : V →ₗ[ℂ] Q) {c : ℂ} (hc : c ≠ 0) :
    TopologicalSpace.induced (c • L)
        (inferInstance : TopologicalSpace Q) =
      TopologicalSpace.induced L
        (inferInstance : TopologicalSpace Q) := by
  let e : Q ≃ₜ Q := Homeomorph.smulOfNeZero c hc
  have hfun : (fun x : V => (c • L) x) = e ∘ L := by
    funext x
    simp [e]
  change TopologicalSpace.induced (fun x : V => (c • L) x) _ = _
  rw [hfun, ← induced_compose, e.induced_eq]

/-- The minimal source-conormal refinement of the complex product clock is unchanged by every
nonzero rescaling of the conormal. -/
theorem sourceConormalRefinedTopology_smul_eq
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (base : TopologicalSpace (ℕ → ℂ)) (L : (ℕ → ℂ) →ₗ[ℂ] Q)
    {c : ℂ} (hc : c ≠ 0) :
    sourceConormalRefinedTopology (K := ℂ) base (c • L) =
      sourceConormalRefinedTopology (K := ℂ) base L := by
  unfold sourceConormalRefinedTopology
  rw [induced_smul_linearMap_eq L hc]

/-- In contrast with the topology, the squared Hermitian response records the normalization of
the conormal exactly. -/
theorem norm_sq_smul_sourceConormal_apply
    {V Q : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : V →ₗ[ℂ] Q) (c : ℂ) (x : V) :
    ‖(c • L) x‖ ^ 2 = ‖c‖ ^ 2 * ‖L x‖ ^ 2 := by
  rw [LinearMap.smul_apply, norm_smul, mul_pow]

end

end GaloisForLFunctions.HTGeometry
