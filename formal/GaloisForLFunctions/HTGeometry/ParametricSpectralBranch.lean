import GaloisForLFunctions.U0.HolomorphicIFT

/-!
# Holomorphic scalar branches over finite-dimensional parameter spaces

This module extends the existing scalar-parameter holomorphic implicit-function theorem to an
arbitrary complete complex Banach parameter space. The result is the analytic branch engine needed
for eigenvalues of Hamiltonians with one independent coupling per interaction edge.
-/

open Filter Topology Complex ContinuousLinearMap Set
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

/-- Holomorphic implicit function theorem with an arbitrary complete complex Banach parameter
space and a scalar root variable. -/
theorem parametric_holo_implicit
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    {f : P × ℂ → ℂ} {p₀ : P} {w₀ : ℂ}
    (hf : AnalyticAt ℂ f (p₀, w₀)) (h0 : f (p₀, w₀) = 0)
    (hfw : (fderiv ℂ f (p₀, w₀)) (0, 1) ≠ 0) :
    ∃ r : P → ℂ, AnalyticAt ℂ r p₀ ∧ r p₀ = w₀ ∧
      (∀ᶠ p in 𝓝 p₀, f (p, r p) = 0) := by
  have cdf : ContDiffAt ℂ ω f (p₀, w₀) := hf.contDiffAt
  have if₂ : (fderiv ℂ f (p₀, w₀) ∘L (.inr ℂ P ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne (by simpa using hfw)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  refine ⟨cdf.implicitFunction hω if₂,
    (cdf.contDiffAt_implicitFunction hω if₂).analyticAt, ?_, ?_⟩
  · exact cdf.implicitFunction_apply_self hω if₂
  · filter_upwards [cdf.eventually_apply_implicitFunction hω if₂] with p hp
    rw [hp, h0]

end GaloisForLFunctions.HTGeometry
