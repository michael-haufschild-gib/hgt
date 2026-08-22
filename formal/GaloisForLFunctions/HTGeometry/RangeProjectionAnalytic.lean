import GaloisForLFunctions.HTGeometry.RangeProjectionDeriv

/-!
# Real analyticity of the closed-range projection

If a family `t ↦ M_t` of bounded operators is real analytic at `t₀` and its Gram operator
`A_{t₀} = Q M_{t₀}* M_{t₀} Q + (1 - Q)` is invertible, then

`P_t = M_t Q A_t⁻¹ Q M_t*`

is real analytic at `t₀` in the operator norm.  The adjoint is only conjugate-linear, so the
statement is about real, not complex, analyticity; inversion contributes its own analyticity
through the geometric series.
-/

open ContinuousLinearMap

namespace HTGeometry

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The adjoint of a real-analytic operator family is real analytic. -/
theorem AnalyticAt.adjoint {M : E → (H →L[ℂ] H)} {t₀ : E} (hM : AnalyticAt ℝ M t₀) :
    AnalyticAt ℝ (fun t => ContinuousLinearMap.adjoint (M t)) t₀ := by
  have h := ((adjointRealCLM (H := H)).analyticAt (M t₀)).comp hM
  simpa [Function.comp_def] using h

variable {Q : H →L[ℂ] H}

/-- The Gram operator of a real-analytic family is real analytic. -/
theorem analyticAt_rangeProjectionGram {M : E → (H →L[ℂ] H)} {t₀ : E}
    (hM : AnalyticAt ℝ M t₀) :
    AnalyticAt ℝ (fun t => rangeProjectionGram Q (M t)) t₀ := by
  have hfun : (fun t => rangeProjectionGram Q (M t))
      = fun t => Q * ContinuousLinearMap.adjoint (M t) * M t * Q + (1 - Q) := rfl
  rw [hfun]
  exact (((( analyticAt_const).mul (AnalyticAt.adjoint hM)).mul hM).mul analyticAt_const).add
    analyticAt_const

/-- **The closed-range projection of a real-analytic family is real analytic.** -/
theorem analyticAt_rangeProjection {M : E → (H →L[ℂ] H)} {t₀ : E}
    (hM : AnalyticAt ℝ M t₀) (hu : IsUnit (rangeProjectionGram Q (M t₀))) :
    AnalyticAt ℝ (fun t => rangeProjection Q (M t)) t₀ := by
  obtain ⟨u, hu'⟩ := hu
  have hgram : AnalyticAt ℝ (fun t => rangeProjectionGram Q (M t)) t₀ :=
    analyticAt_rangeProjectionGram hM
  have hinv : AnalyticAt ℝ (fun t => Ring.inverse (rangeProjectionGram Q (M t))) t₀ := by
    have hbase : AnalyticAt ℝ (Ring.inverse (M₀ := H →L[ℂ] H))
        (rangeProjectionGram Q (M t₀)) := by
      rw [← hu']
      exact analyticAt_inverse u
    have hcomp := AnalyticAt.comp (g := (Ring.inverse (M₀ := H →L[ℂ] H)))
      (f := fun t => rangeProjectionGram Q (M t)) hbase hgram
    simpa [Function.comp_def] using hcomp
  have hfun : (fun t => rangeProjection Q (M t))
      = fun t => M t * Q * Ring.inverse (rangeProjectionGram Q (M t)) * Q *
        ContinuousLinearMap.adjoint (M t) := rfl
  rw [hfun]
  exact ((((hM.mul analyticAt_const).mul hinv).mul analyticAt_const).mul
    (AnalyticAt.adjoint hM))

end

end HTGeometry
