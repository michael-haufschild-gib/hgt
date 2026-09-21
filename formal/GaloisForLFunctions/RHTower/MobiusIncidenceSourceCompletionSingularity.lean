import GaloisForLFunctions.RHTower.MobiusIncidenceKMSCofinalResponse

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

namespace RHTower

/-- The unique literal correction taking the universal squarefree-incidence KMS response to
the completed prime--polar--Gamma source. -/
def mobiusIncidenceSourceCompletion (z : ℂ) : ℂ :=
  continuedPrimeArchSourceRelativeTrace z - mobiusIncidenceUniversalGapResponse z

private theorem tendsto_posImag_nhdsWithin_zero : Tendsto
    (fun eta : ℝ => Complex.I * (eta : ℂ))
    (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℂ)) := by
  have hcont : ContinuousAt (fun eta : ℝ => Complex.I * (eta : ℂ)) 0 := by
    fun_prop
  simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- A source-faithful correction to the universal incidence response cannot be lower order
than the centered clock.  It must cancel the logarithmically divergent incidence slope. -/
theorem not_tendsto_mobiusIncidenceSourceCompletion_I_mul_div_zero :
    ¬ Tendsto
      (fun eta : ℝ =>
        mobiusIncidenceSourceCompletion (Complex.I * eta) /
          (Complex.I * eta))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  intro hcompletion
  have hmap_mem : ∀ᶠ eta : ℝ in nhdsWithin 0 (Ioi 0),
      Complex.I * (eta : ℂ) ∈ ({0} : Set ℂ)ᶜ := by
    filter_upwards [self_mem_nhdsWithin] with eta heta
    simp only [mem_compl_iff, mem_singleton_iff]
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast heta.ne')
  have hmap : Tendsto
      (fun eta : ℝ => Complex.I * (eta : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 ({0} : Set ℂ)ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_posImag_nhdsWithin_zero, hmap_mem⟩
  have htraceFinite :=
    _root_.HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero
      analyticAt_continuedPrimeArchSourceRelativeTrace.differentiableAt
      continuedPrimeArchSourceRelativeTrace_zero
  have htraceQuotient : Tendsto
      (fun eta : ℝ =>
        continuedPrimeArchSourceRelativeTrace (Complex.I * eta) /
          (Complex.I * eta))
      (nhdsWithin 0 (Ioi 0))
      (nhds (deriv continuedPrimeArchSourceRelativeTrace 0)) := by
    simpa only [Function.comp_def, sub_zero] using htraceFinite.comp hmap
  have hgap : Tendsto
      (fun eta : ℝ =>
        mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
          (Complex.I * eta))
      (nhdsWithin 0 (Ioi 0))
      (nhds (deriv continuedPrimeArchSourceRelativeTrace 0)) := by
    have hraw := htraceQuotient.sub hcompletion
    have hrewrite :
        (fun eta : ℝ =>
          continuedPrimeArchSourceRelativeTrace (Complex.I * eta) /
              (Complex.I * eta) -
            mobiusIncidenceSourceCompletion (Complex.I * eta) /
              (Complex.I * eta)) =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun eta : ℝ =>
          mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
            (Complex.I * eta)) := by
      filter_upwards [self_mem_nhdsWithin] with eta heta
      unfold mobiusIncidenceSourceCompletion
      have heta0 : (Complex.I * (eta : ℂ)) ≠ 0 :=
        mul_ne_zero Complex.I_ne_zero (by exact_mod_cast heta.ne')
      field_simp
      ring
    simpa using hraw.congr' hrewrite
  exact
    (not_tendsto_mobiusIncidenceUniversalGapResponse_I_mul_div_nhds
      (deriv continuedPrimeArchSourceRelativeTrace 0)) hgap

/-- The literal source correction is nonremovable at the centered clock.  Consequently the
needed prime--polar--Gamma completion cannot arise from an analytic KMS counterterm. -/
theorem not_differentiableAt_mobiusIncidenceSourceCompletion_zero :
    ¬ DifferentiableAt ℂ mobiusIncidenceSourceCompletion 0 := by
  intro hcompletion
  have hsource : DifferentiableAt ℂ continuedPrimeArchSourceRelativeTrace 0 :=
    analyticAt_continuedPrimeArchSourceRelativeTrace.differentiableAt
  have hgap : DifferentiableAt ℂ mobiusIncidenceUniversalGapResponse 0 := by
    rw [show mobiusIncidenceUniversalGapResponse =
        continuedPrimeArchSourceRelativeTrace - mobiusIncidenceSourceCompletion by
      funext z
      change mobiusIncidenceUniversalGapResponse z =
        continuedPrimeArchSourceRelativeTrace z -
          (continuedPrimeArchSourceRelativeTrace z -
            mobiusIncidenceUniversalGapResponse z)
      ring]
    exact hsource.sub hcompletion
  exact not_differentiableAt_mobiusIncidenceUniversalGapResponse_zero hgap

/-- No source-faithful global completion of the universal squarefree-incidence response may
be differentiable at the centered clock.  A successful producer therefore has to retain a
signed prime--polar--Gamma singular cancellation, rather than append an ordinary analytic
thermodynamic correction. -/
theorem not_exists_differentiableAt_mobiusIncidence_sourceFaithfulCompletion :
    ¬ ∃ C : ℂ → ℂ,
      DifferentiableAt ℂ C 0 ∧
      ∀ z : ℂ,
        continuedPrimeArchSourceRelativeTrace z =
          mobiusIncidenceUniversalGapResponse z + C z := by
  rintro ⟨C, hC, hbridge⟩
  have hsource : DifferentiableAt ℂ continuedPrimeArchSourceRelativeTrace 0 :=
    analyticAt_continuedPrimeArchSourceRelativeTrace.differentiableAt
  have hgap : DifferentiableAt ℂ mobiusIncidenceUniversalGapResponse 0 := by
    rw [show mobiusIncidenceUniversalGapResponse =
        continuedPrimeArchSourceRelativeTrace - C by
      funext z
      change mobiusIncidenceUniversalGapResponse z =
        continuedPrimeArchSourceRelativeTrace z - C z
      rw [hbridge z]
      ring]
    exact hsource.sub hC
  exact not_differentiableAt_mobiusIncidenceUniversalGapResponse_zero hgap

end RHTower
