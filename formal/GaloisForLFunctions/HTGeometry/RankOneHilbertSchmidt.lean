import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# Rank-one operators are Hilbert--Schmidt

A rank-one operator `x ↦ φ(x) • v` has Hilbert--Schmidt norm `‖φ‖·‖v‖`: Riesz represents the
functional, and Parseval turns the square-summability of its coefficients into the norm of the
representing vector.  This is the base case from which finite rank inherits the Hilbert--Schmidt
property, and hence trace-class membership in factorization form.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The coefficients of a bounded functional along a Hilbert basis are square-summable. -/
theorem summable_norm_apply_sq {ι : Type*} (b : HilbertBasis ι 𝕜 E) (φ : E →L[𝕜] 𝕜) :
    Summable (fun i => ‖φ (b i)‖ ^ (2 : ℕ)) := by
  classical
  set u : E := (InnerProductSpace.toDual 𝕜 E).symm φ with hu
  have hval : ∀ i, φ (b i) = inner 𝕜 u (b i) := by
    intro i
    rw [hu, InnerProductSpace.toDual_symm_apply]
  have hconj : ∀ i, ‖φ (b i)‖ = ‖inner 𝕜 (b i) u‖ := by
    intro i
    rw [hval i, ← inner_conj_symm, RCLike.norm_conj]
  simpa only [hconj] using b.summable_norm_inner_sq u

omit [CompleteSpace F] in
/-- **A rank-one operator is Hilbert--Schmidt.** -/
theorem isHilbertSchmidt_smulRight (φ : E →L[𝕜] 𝕜) (v : F) :
    ContinuousLinearMap.IsHilbertSchmidt (φ.smulRight v) := by
  have hval : ∀ i, ‖(φ.smulRight v) (ContinuousLinearMap.hsBasis 𝕜 E i)‖ ^ (2 : ℕ)
      = ‖φ (ContinuousLinearMap.hsBasis 𝕜 E i)‖ ^ (2 : ℕ) * ‖v‖ ^ (2 : ℕ) := by
    intro i
    rw [ContinuousLinearMap.smulRight_apply, norm_smul, mul_pow]
  show Summable (fun i => ‖(φ.smulRight v) (ContinuousLinearMap.hsBasis 𝕜 E i)‖ ^ (2 : ℕ))
  simp only [hval]
  exact (summable_norm_apply_sq (ContinuousLinearMap.hsBasis 𝕜 E) φ).mul_right _

end

end GaloisForLFunctions.HTGeometry
