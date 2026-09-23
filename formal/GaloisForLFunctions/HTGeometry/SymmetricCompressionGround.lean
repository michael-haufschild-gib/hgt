import GaloisForLFunctions.HTGeometry.GroundGapCompression
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Compressions of a symmetric operator and their ground states

The compression of a symmetric operator `T` to a subspace `U` with an orthogonal projection is
again symmetric, and its quadratic form on `U` is the restriction of the quadratic form of `T`.
Consequently every statement about Rayleigh quotients transfers verbatim between the operator and
its compression.

On a finite-dimensional subspace the unit sphere is compact, so a compressed ground state exists;
and if the ambient operator has a spectral gap `Δ` above a ground vector `ξ`, the compressed ground
energy stays below `λ + Δ` exactly when the compressed ground line is unique.  This is the
variational half of an approximation argument: the compressed grounds are approximate ground states
of the ambient operator, hence converge to `ξ`.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The compression of a linear operator to a subspace carrying an orthogonal projection. -/
def compress (T : E →ₗ[ℝ] E) (U : Submodule ℝ E) [U.HasOrthogonalProjection] : U →ₗ[ℝ] U :=
  (U.orthogonalProjectionOnto : E →L[ℝ] U).toLinearMap ∘ₗ T ∘ₗ U.subtype

theorem inner_compress (T : E →ₗ[ℝ] E) (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (v w : U) :
    (inner ℝ (compress T U v) w : ℝ) = inner ℝ (T (v : E)) (w : E) := by
  rw [compress]
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    Submodule.coe_subtype]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w (T (v : E))

theorem compress_isSymmetric (T : E →ₗ[ℝ] E) (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (hsymm : ∀ x y : E, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y)) (v w : U) :
    (inner ℝ (compress T U v) w : ℝ) = inner ℝ v (compress T U w) :=
  calc (inner ℝ (compress T U v) w : ℝ)
      = inner ℝ (T (v : E)) (w : E) := inner_compress T U v w
    _ = inner ℝ (v : E) (T (w : E)) := hsymm _ _
    _ = inner ℝ (T (w : E)) (v : E) := real_inner_comm _ _
    _ = inner ℝ (compress T U w) v := (inner_compress T U w v).symm
    _ = inner ℝ v (compress T U w) := real_inner_comm _ _

/-! ## The compressed ground state -/

/-- **Existence of a compressed ground state.**  On a finite-dimensional subspace the unit sphere
is compact, so the Rayleigh quotient attains its minimum. -/
theorem exists_compressed_ground (T : E →ₗ[ℝ] E) (U : Submodule ℝ E)
    [FiniteDimensional ℝ U] (hne : ∃ x : U, ‖x‖ = 1) :
    ∃ η : U, ‖η‖ = 1 ∧ ∀ v : U, ‖v‖ = 1 →
      (inner ℝ (T (η : E)) (η : E) : ℝ) ≤ inner ℝ (T (v : E)) (v : E) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Set U, S = Metric.sphere (0 : U) 1 := ⟨_, rfl⟩
  have hcompact : IsCompact S := by
    rw [hS]
    exact isCompact_sphere (0 : U) 1
  have hnonempty : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by rw [hS]; simpa [Metric.mem_sphere] using hx⟩
  have hcont : ContinuousOn (fun v : U => (inner ℝ (T (v : E)) (v : E) : ℝ)) S := by
    have : Continuous fun v : U => (inner ℝ (T (v : E)) (v : E) : ℝ) := by
      have h1 : Continuous fun v : U => ((v : E)) := continuous_subtype_val
      have h2 : Continuous fun v : U => T (v : E) :=
        (T ∘ₗ U.subtype).continuous_of_finiteDimensional
      exact continuous_inner.comp (h2.prodMk h1)
    exact this.continuousOn
  obtain ⟨η, hηS, hmin⟩ := hcompact.exists_isMinOn hnonempty hcont
  refine ⟨η, ?_, ?_⟩
  · rw [hS] at hηS
    simpa [Metric.mem_sphere] using hηS
  · intro v hv
    have hvS : v ∈ S := by
      rw [hS]
      simpa [Metric.mem_sphere] using hv
    exact hmin hvS

/-! ## The compressed ground is simple below the gap -/

/-- **Simplicity of a compressed ground below the gap.**  If the ambient gap threshold `μ` is not
reached on the compressed ground eigenspace, that eigenspace is at most a line. -/
theorem finrank_le_one_of_compressed_rayleigh_lt (T : E →ₗ[ℝ] E) {ξ : E} {μ : ℝ}
    (hgap : ∀ v : E, (inner ℝ ξ v : ℝ) = 0 → μ * ‖v‖ ^ (2 : ℕ) ≤ inner ℝ (T v) v)
    {U : Submodule ℝ E} (hU : ∀ v ∈ U, v ≠ 0 → (inner ℝ (T v) v : ℝ) < μ * ‖v‖ ^ (2 : ℕ)) :
    Module.finrank ℝ U ≤ 1 :=
  finrank_le_one_of_rayleigh_lt T hgap hU

end GaloisForLFunctions.HTGeometry

end
