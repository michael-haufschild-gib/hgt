import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Scalar renormalization of Rayleigh excess

Adding a real scalar multiple of the identity shifts every Rayleigh value and every spectral
energy by the same scalar.  It therefore leaves the spectral gap, Rayleigh excess, and their ratio
unchanged.  This is the exact consumer for the universal `log c` identity term in the CCM
archimedean form: only the scalar-renormalized remainder can affect ground-vector selection.
-/

open scoped InnerProductSpace

namespace RHTower

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A real scalar identity shift adds that scalar to every nonzero Rayleigh quotient. -/
theorem rayleighQuotient_add_real_smul_id
    (T : E →L[𝕜] E) (r : ℝ) (x : E) (hx : x ≠ 0) :
    (T + (r : 𝕜) • ContinuousLinearMap.id 𝕜 E).rayleighQuotient x =
      T.rayleighQuotient x + r := by
  rw [ContinuousLinearMap.rayleighQuotient_add]
  simp only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
    inner_self_eq_norm_sq]
  field_simp

/-- Subtracting the correspondingly shifted ground energy removes a scalar identity shift from
the Rayleigh excess exactly. -/
theorem rayleighExcess_add_real_smul_id
    (T : E →L[𝕜] E) (r epsilon : ℝ) (x : E) (hx : x ≠ 0) :
    (T + (r : 𝕜) • ContinuousLinearMap.id 𝕜 E).rayleighQuotient x -
        (epsilon + r) =
      T.rayleighQuotient x - epsilon := by
  rw [rayleighQuotient_add_real_smul_id T r x hx]
  ring

/-- A common scalar shift cancels from a spectral gap. -/
theorem spectralGap_add_cancel (epsilon₀ epsilon₁ r : ℝ) :
    (epsilon₁ + r) - (epsilon₀ + r) = epsilon₁ - epsilon₀ := by
  ring

/-- The dimensionless Rayleigh-excess-to-gap ratio is exactly invariant under a real scalar
identity shift. -/
theorem rayleighExcessRatio_add_real_smul_id
    (T : E →L[𝕜] E) (r epsilon₀ epsilon₁ : ℝ) (x : E) (hx : x ≠ 0) :
    ((T + (r : 𝕜) • ContinuousLinearMap.id 𝕜 E).rayleighQuotient x -
          (epsilon₀ + r)) /
        ((epsilon₁ + r) - (epsilon₀ + r)) =
      (T.rayleighQuotient x - epsilon₀) / (epsilon₁ - epsilon₀) := by
  rw [rayleighQuotient_add_real_smul_id T r x hx]
  ring

end RHTower
