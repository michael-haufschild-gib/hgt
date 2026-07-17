import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue
import GaloisForLFunctions.RHTower.RayleighGapProjective

/-!
# Rayleigh-gap control of projective quantum-Fisher energy

The unit-vector defect controlled in the existing Rayleigh-gap route is exactly the projective
Gram tangent energy, hence one quarter of the corresponding unit-mass pure-state quantum Fisher
value.  The adapter below lets spectral-gap estimates consume the new invariant value directly.
-/

open scoped InnerProductSpace

namespace RHTower

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Existing Rayleigh-gap coercivity directly bounds the projective quantum tangent energy. -/
theorem projectiveQuantumTangentEnergy_le_rayleighExcess_div_gap
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    {v g : E} {epsilon gap : ℝ}
    (hv : ‖v‖ = 1) (hg : ‖g‖ = 1)
    (hTv : T v = (epsilon : 𝕜) • v) (hgap : 0 < gap)
    (hcoercive : gap * ‖g - inner 𝕜 v g • v‖ ^ 2 ≤
      (T - (epsilon : 𝕜) • ContinuousLinearMap.id 𝕜 E).reApplyInnerSelf
        (g - inner 𝕜 v g • v)) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := 𝕜) v g ≤
      (T.rayleighQuotient g - epsilon) / gap := by
  rw [HTGeometry.projectiveGramTangentEnergy_eq_unit_projectiveDefect
    (𝕜 := 𝕜) hv hg]
  exact one_sub_norm_inner_sq_le_rayleighExcess_div_gap
    T hT hv hg hTv hgap hcoercive

/-- The existing phase-aligned distance theorem can use projective quantum tangent energy as its
exact defect value. -/
theorem exists_unitScalar_norm_sub_sq_le_two_projectiveQuantumTangentEnergy
    {v g : E} (hv : ‖v‖ = 1) (hg : ‖g‖ = 1) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖g - c • v‖ ^ 2 ≤
        2 * HTGeometry.projectiveGramTangentEnergy (𝕜 := 𝕜) v g := by
  simpa [HTGeometry.projectiveGramTangentEnergy_eq_unit_projectiveDefect
    (𝕜 := 𝕜) hv hg] using
    exists_unitScalar_norm_sub_sq_le_two_projectiveDefect (𝕜 := 𝕜) hv hg

end RHTower
