import GaloisForLFunctions.HTGeometry.FactorThroughRange
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Extend
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Basic

/-!
# A complex functional realizing a real functional dominated by a restriction

A real functional dominated by a constant times the supremum norm of the image of a linear map into
`C(K, ℂ)` factors through the range of that map, extends by Hahn–Banach to the whole space, and
complexifies: the resulting complex functional has the original functional as its real part on the
image.

* `GaloisForLFunctions.HTGeometry.exists_complex_functional_of_bound`.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **A dominated real functional is the real part of a complex functional on `C(K, ℂ)`.** -/
theorem exists_complex_functional_of_bound {M : Type*} [AddCommGroup M] [Module ℝ M]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (T : M →ₗ[ℝ] C(K, ℂ)) (f : M →ₗ[ℝ] ℝ)
    (C : ℝ) (hbd : ∀ x : M, |f x| ≤ C * ‖T x‖) :
    ∃ L : C(K, ℂ) →L[ℂ] ℂ, ∀ x : M, (L (T x)).re = f x := by
  have hker : ∀ x : M, T x = 0 → f x = 0 := by
    intro x hx
    have h := hbd x
    rw [hx, norm_zero, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  set φ : (LinearMap.range T) →L[ℝ] ℝ := factorRangeCLM T f hker C hbd with hφ
  obtain ⟨Φ, hΦ, -⟩ := exists_extension_norm_eq (𝕜 := ℝ) (LinearMap.range T) φ
  refine ⟨StrongDual.extendRCLike (𝕜 := ℂ) Φ, fun x => ?_⟩
  have hre : RCLike.re ((StrongDual.extendRCLike (𝕜 := ℂ) Φ) (T x)) = Φ (T x) :=
    StrongDual.re_extendRCLike_apply Φ (T x)
  have hmem : T x ∈ LinearMap.range T := ⟨x, rfl⟩
  have hval : Φ (T x) = φ ⟨T x, hmem⟩ := hΦ ⟨T x, hmem⟩
  have hφval : φ ⟨T x, hmem⟩ = f x := factorRangeCLM_apply_of_eq T f hker C hbd rfl
  rw [← hφval, ← hval]
  exact hre

end GaloisForLFunctions.HTGeometry
