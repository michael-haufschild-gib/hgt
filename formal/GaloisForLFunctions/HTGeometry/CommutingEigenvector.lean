import Mathlib

/-!
# Commuting operators and a simple eigenvalue

If two operators commute, each eigenspace of the first is invariant under the second.  When that
eigenspace is one dimensional, the second operator therefore acts on it by a scalar: the eigenvector
of the first is automatically an eigenvector of the second.

This is the logical step that converts an integral eigen-equation into a differential one.
Commutation alone gives only that `L f` is again an eigenvector of the integral operator with the
same eigenvalue; concluding `L f = mu • f` needs the eigenvalue to be simple.
-/

namespace HTGeometry

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- **A commuting operator preserves an eigenspace.** -/
theorem eigen_of_commute {T L : V →ₗ[𝕜] V} (hcomm : ∀ v : V, T (L v) = L (T v)) {χ : 𝕜} {f : V}
    (hf : T f = χ • f) : T (L f) = χ • L f := by
  rw [hcomm, hf, map_smul]

/-- **A simple eigenvalue forces the commuting operator to act by a scalar.** -/
theorem exists_smul_of_commute_of_eigenspace_le_span {T L : V →ₗ[𝕜] V}
    (hcomm : ∀ v : V, T (L v) = L (T v)) {χ : 𝕜} {f : V} (hf : T f = χ • f)
    (hsimple : ∀ g : V, T g = χ • g → ∃ a : 𝕜, g = a • f) :
    ∃ μ : 𝕜, L f = μ • f :=
  hsimple (L f) (eigen_of_commute hcomm hf)

/-- The same statement read as an eigenvalue equation for `L`. -/
theorem isEigenvector_of_commute_of_simple {T L : V →ₗ[𝕜] V}
    (hcomm : ∀ v : V, T (L v) = L (T v)) {χ : 𝕜} {f : V} (hf : T f = χ • f)
    (hsimple : ∀ g : V, T g = χ • g → ∃ a : 𝕜, g = a • f) :
    ∃ μ : 𝕜, L f - μ • f = 0 := by
  obtain ⟨μ, hμ⟩ := exists_smul_of_commute_of_eigenspace_le_span hcomm hf hsimple
  exact ⟨μ, by rw [hμ, sub_self]⟩

end HTGeometry
