import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Singular finite Gram prediction over real and complex Hilbert spaces

The Gram operator is invertible on the orthogonal complement of its kernel.
Its inverse there gives optimal prediction without any nonsingularity assumption.
The exact error decomposition classifies every minimizer, including redundant
observations and zero noise.
-/

noncomputable section
open scoped InnerProductSpace
namespace HilbertMetric.Correlation
variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

local instance : CompleteSpace V := FiniteDimensional.complete 𝕜 V

/-- Observation Gram operator, including singular observation families. -/
def finiteObservationGram (Φ : V →L[𝕜] H) : V →ₗ[𝕜] V :=
  (Φ.adjoint.comp Φ : V →L[𝕜] V)

private theorem inner_finiteObservationGram (Φ : V →L[𝕜] H) (x y : V) :
    ⟪x, finiteObservationGram Φ y⟫_𝕜 = ⟪Φ x, Φ y⟫_𝕜 :=
  ContinuousLinearMap.adjoint_inner_right Φ x (Φ y)

/-- The coefficient directions visible to the observations. -/
abbrev observationSector (Φ : V →L[𝕜] H) : Submodule 𝕜 V :=
  (LinearMap.ker (finiteObservationGram Φ))ᗮ

private theorem gram_mem_observationSector (Φ : V →L[𝕜] H) (x : V) :
    finiteObservationGram Φ x ∈ observationSector Φ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hz0 : Φ z = 0 := by
    have h := inner_finiteObservationGram Φ z z
    rw [LinearMap.mem_ker.mp hz, inner_zero_right] at h
    exact inner_self_eq_zero.mp h.symm
  rw [inner_finiteObservationGram, hz0, inner_zero_left]

private def observationSectorMap (Φ : V →L[𝕜] H) :
    observationSector Φ →ₗ[𝕜] observationSector Φ :=
  ((finiteObservationGram Φ).domRestrict _).codRestrict _
    (fun x => gram_mem_observationSector Φ x)

private theorem observationSectorMap_injective (Φ : V →L[𝕜] H) :
    Function.Injective (observationSectorMap Φ) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have h0 : finiteObservationGram Φ x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  have hmem : (x : V) ∈ LinearMap.ker (finiteObservationGram Φ) ⊓ observationSector Φ :=
    ⟨h0, x.property⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact (Submodule.mem_bot 𝕜).mpr (Subtype.ext hmem)

private def observationSectorEquiv (Φ : V →L[𝕜] H) :
    observationSector Φ ≃ₗ[𝕜] observationSector Φ :=
  LinearEquiv.ofBijective (observationSectorMap Φ)
    ⟨observationSectorMap_injective Φ,
      LinearMap.injective_iff_surjective.mp (observationSectorMap_injective Φ)⟩

/-- The Gram pseudoinverse uses the inverse only on the visible coefficient sector. -/
def finiteGramPseudoInverse (Φ : V →L[𝕜] H) : V →ₗ[𝕜] V :=
  (observationSector Φ).subtype ∘ₗ (observationSectorEquiv Φ).symm.toLinearMap ∘ₗ
    ((observationSector Φ).orthogonalProjectionOnto : V →ₗ[𝕜] observationSector Φ)

private theorem gram_pseudoInverse (Φ : V →L[𝕜] H) (y : V) :
    finiteObservationGram Φ (finiteGramPseudoInverse Φ y) =
      (observationSector Φ).starProjection y := by
  exact congrArg Subtype.val
    ((observationSectorEquiv Φ).apply_symm_apply ((observationSector Φ).orthogonalProjectionOnto y))

/-- Optimal coefficients chosen perpendicular to the invisible coefficient directions. -/
def finitePredictionCoefficients (Φ : V →L[𝕜] H) (u : H) : V :=
  finiteGramPseudoInverse Φ (Φ.adjoint u)

/-- The normal equations are solvable even when the Gram operator is singular. -/
theorem finitePrediction_normal (Φ : V →L[𝕜] H) (u : H) :
    finiteObservationGram Φ (finitePredictionCoefficients Φ u) = Φ.adjoint u := by
  rw [finitePredictionCoefficients, gram_pseudoInverse]
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [Submodule.mem_orthogonal]
  intro z hz
  have h := inner_finiteObservationGram Φ z z
  rw [LinearMap.mem_ker.mp hz, inner_zero_right] at h
  have hz0 : Φ z = 0 := inner_self_eq_zero.mp h.symm
  rw [ContinuousLinearMap.adjoint_inner_right, hz0, inner_zero_left]

/-- The residual is orthogonal to every observation, including redundant families. -/
theorem finitePrediction_orthogonal (Φ : V →L[𝕜] H) (u : H) (v : V) :
    ⟪u - Φ (finitePredictionCoefficients Φ u), Φ v⟫_𝕜 = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, map_sub]
  change ⟪Φ.adjoint u - finiteObservationGram Φ (finitePredictionCoefficients Φ u), v⟫_𝕜 = 0
  rw [finitePrediction_normal, sub_self, inner_zero_left]

/-- Exact excess prediction error is the squared observed coefficient displacement. -/
theorem finitePrediction_error_decomposition (Φ : V →L[𝕜] H) (u : H) (v : V) :
    ‖u - Φ v‖ ^ 2 = ‖u - Φ (finitePredictionCoefficients Φ u)‖ ^ 2 +
      ‖Φ (v - finitePredictionCoefficients Φ u)‖ ^ 2 := by
  have he : u - Φ v = (u - Φ (finitePredictionCoefficients Φ u)) -
      Φ (v - finitePredictionCoefficients Φ u) := by rw [map_sub]; abel
  rw [he, norm_sub_sq (𝕜 := 𝕜), finitePrediction_orthogonal, RCLike.zero_re, mul_zero, sub_zero]

/-- All minimizers differ exactly by an invisible coefficient vector. -/
theorem finitePrediction_minimizer_iff (Φ : V →L[𝕜] H) (u : H) (v : V) :
    (∀ w : V, ‖u - Φ v‖ ^ 2 ≤ ‖u - Φ w‖ ^ 2) ↔
      Φ (v - finitePredictionCoefficients Φ u) = 0 := by
  constructor
  · intro hv
    have h := hv (finitePredictionCoefficients Φ u)
    rw [finitePrediction_error_decomposition] at h
    have hz : ‖Φ (v - finitePredictionCoefficients Φ u)‖ ^ 2 = 0 := by
      nlinarith only [sq_nonneg ‖Φ (v - finitePredictionCoefficients Φ u)‖, h]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro hv w
    rw [finitePrediction_error_decomposition Φ u v,
      finitePrediction_error_decomposition Φ u w, hv, norm_zero, zero_pow (by omega : 2 ≠ 0), add_zero]
    exact le_add_of_nonneg_right (sq_nonneg _)

end HilbertMetric.Correlation

