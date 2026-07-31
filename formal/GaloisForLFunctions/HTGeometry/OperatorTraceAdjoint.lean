import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# Conjugation law for the operator trace

The diagonal sum defining `opTrace` sends the adjoint to the conjugate, termwise and without any
summability hypothesis, because `⟪e, T† e⟫ = conj ⟪e, T e⟫` on every basis vector.  Consequently an
operator equal to its own adjoint has a conjugation-invariant trace, and over `ℂ` that trace is
real.
-/

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The operator trace sends the adjoint to the conjugate. -/
theorem opTrace_adjoint (T : E →L[𝕜] E) :
    opTrace (ContinuousLinearMap.adjoint T) = star (opTrace T) := by
  rw [opTrace, opTrace, tsum_star]
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h := inner_conj_symm (𝕜 := 𝕜) (T (hsBasis 𝕜 E i)) (hsBasis 𝕜 E i)
  rw [starRingEnd_apply] at h
  exact h.symm

/-- An operator equal to its own adjoint has conjugation-invariant trace. -/
theorem star_opTrace_of_adjoint_eq {T : E →L[𝕜] E}
    (hT : ContinuousLinearMap.adjoint T = T) :
    star (opTrace T) = opTrace T := by
  rw [← opTrace_adjoint T, hT]

/-- Over the complex field the trace of a self-adjoint operator is real. -/
theorem im_opTrace_eq_zero_of_adjoint_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : F →L[ℂ] F} (hT : ContinuousLinearMap.adjoint T = T) :
    (opTrace T).im = 0 := by
  have h := star_opTrace_of_adjoint_eq hT
  have him : -(opTrace T).im = (opTrace T).im := by
    simpa using congrArg Complex.im h
  linarith

/-- Over the complex field the trace of a self-adjoint operator is its own real part. -/
theorem opTrace_eq_re_of_adjoint_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : F →L[ℂ] F} (hT : ContinuousLinearMap.adjoint T = T) :
    opTrace T = ((opTrace T).re : ℂ) := by
  refine Complex.ext rfl ?_
  simp [im_opTrace_eq_zero_of_adjoint_eq hT]

end ContinuousLinearMap
