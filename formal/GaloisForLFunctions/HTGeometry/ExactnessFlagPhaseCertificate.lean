import GaloisForLFunctions.HTGeometry.ExactnessFlagProvenanceTopology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.RCLike.Extend

/-!
# Continuous phase certificates for nonboundary classes

In a Hausdorff locally convex space with a closed boundary subspace, a vector represents a nonzero
class of the spectral quotient exactly when some continuous covector annihilates the whole boundary
space and does not annihilate the vector.

The certificate is produced by geometric Hahn–Banach separation of the point from the closed
boundary subspace: a functional bounded below on a subspace vanishes on it.  Over `ℝ` this is
immediate; over an arbitrary `RCLike` field the real certificate is upgraded by the canonical
real-to-`RCLike` extension of continuous functionals.

The certificate is an existence statement only.  It selects no canonical covector and carries no
covariance, so it does not by itself supply a source-canonical phase reporter.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ExFlag

open RCLike

/-! ## The real case -/

section Real

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- **Continuous phase certificate over the reals.**  A vector lies outside a closed subspace
exactly when a continuous functional annihilating that subspace does not annihilate the vector. -/
theorem exists_real_phase_certificate {B : Submodule ℝ E} (hB : IsClosed (B : Set E)) {v : E} :
    v ∉ B ↔ ∃ φ : StrongDual ℝ E, (∀ b ∈ B, φ b = 0) ∧ φ v ≠ 0 := by
  constructor
  · intro hv
    obtain ⟨f, u, hfv, hfb⟩ := geometric_hahn_banach_point_closed B.convex hB hv
    have hzero : ∀ b ∈ B, f b = 0 := by
      intro b hb
      by_contra hfb0
      have hmem : ((u - 1) / f b) • b ∈ B := B.smul_mem _ hb
      have hlt := hfb _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfb0] at hlt
      linarith
    have hu : u < 0 := by
      have h0 := hfb 0 B.zero_mem
      simpa using h0
    refine ⟨f, hzero, ?_⟩
    intro h
    rw [h] at hfv
    linarith
  · rintro ⟨φ, hφ, hv⟩ hvB
    exact hv (hφ v hvB)

end Real

/-! ## The real or complex case -/

section RCLikeScalars

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [ContinuousConstSMul 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- **Continuous phase certificate.**  For a closed boundary subspace of a Hausdorff locally convex
real or complex space, a cycle represents a nonzero spectral class exactly when some continuous
covector annihilates the boundary space and does not annihilate the cycle. -/
theorem exists_phase_certificate {B : Submodule 𝕜 E} (hB : IsClosed (B : Set E)) {v : E} :
    v ∉ B ↔ ∃ φ : StrongDual 𝕜 E, (∀ b ∈ B, φ b = 0) ∧ φ v ≠ 0 := by
  constructor
  · intro hv
    obtain ⟨f, hf0, hfv⟩ :=
      (exists_real_phase_certificate (B := B.restrictScalars ℝ) hB).1 hv
    refine ⟨StrongDual.extendRCLike f, fun b hb => ?_, ?_⟩
    · rw [StrongDual.extendRCLike_apply, hf0 b hb, hf0 ((I : 𝕜) • b) (B.smul_mem _ hb)]
      simp
    · intro h
      refine hfv ?_
      have hre := StrongDual.re_extendRCLike_apply (𝕜 := 𝕜) f v
      rw [h, map_zero] at hre
      exact hre.symm
  · rintro ⟨φ, hφ, hv⟩ hvB
    exact hv (hφ v hvB)

/-- **A cycle survives in the spectral quotient exactly when it has a continuous phase
certificate.** -/
theorem mem_survival_iff_exists_phase_certificate (p : ExFlag 𝕜 E)
    (hB : IsClosed (p.boundary : Set E)) {v : E} (hv : v ∈ p.cycle) :
    p ∈ survival v ↔ ∃ φ : StrongDual 𝕜 E, (∀ b ∈ p.boundary, φ b = 0) ∧ φ v ≠ 0 := by
  rw [mem_survival_iff]
  exact ⟨fun h => (exists_phase_certificate hB).1 h.2,
    fun h => ⟨hv, (exists_phase_certificate hB).2 h⟩⟩

end RCLikeScalars

end ExFlag

end GaloisForLFunctions.HTGeometry
