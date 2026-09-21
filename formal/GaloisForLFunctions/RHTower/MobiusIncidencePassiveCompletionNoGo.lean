import GaloisForLFunctions.RHTower.MobiusIncidenceSourceCompletionSingularity
import GaloisForLFunctions.RHTower.PrimeArchEntropyProductionParityBridge

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- On the positive imaginary clock, every finite Hermitian entropy-production response has
nonpositive real normalized slope.  A passive KMS channel therefore cannot cancel a negative
incidence slope. -/
theorem finiteKMSEntropyProductionTransitionPassiveResponse_I_mul_div_re_nonpos
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    {eta : ℝ} (heta : 0 < eta) :
    (HTGeometry.finiteTransitionPassiveResponse
      (finiteKMSEntropyProductionTransitionIntensity β energy amplitude) energy
      (Complex.I * eta) / (Complex.I * eta)).re ≤ 0 := by
  let response : ℂ := HTGeometry.finiteTransitionPassiveResponse
    (finiteKMSEntropyProductionTransitionIntensity β energy amplitude) energy
    (Complex.I * eta)
  have hfixed : (-(starRingEnd ℂ) (Complex.I * (eta : ℂ))) =
      Complex.I * eta := by
    rw [map_mul]
    simp only [Complex.conj_I, Complex.conj_ofReal]
    ring
  have hcov := finiteKMSEntropyProductionTransitionPassiveResponse_negConj
    β energy amplitude hHermitian (Complex.I * eta)
  rw [hfixed] at hcov
  have hre : response.re = 0 := by
    change (HTGeometry.finiteTransitionPassiveResponse
      (finiteKMSEntropyProductionTransitionIntensity β energy amplitude) energy
      (Complex.I * eta)).re = 0
    have := congrArg Complex.re hcov
    simp only [Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : response.im ≤ 0 := by
    exact HTGeometry.finiteTransitionPassiveResponse_im_nonpos _ energy
      (finiteKMSEntropyProductionTransitionIntensity_nonneg
        β energy amplitude hHermitian)
      (by simp [heta])
  change (response / (Complex.I * eta)).re ≤ 0
  have hIeta_im : (Complex.I * (eta : ℂ)).im = eta := by simp
  rw [Complex.div_re]
  rw [hre, zero_mul, zero_div, zero_add, hIeta_im]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg him heta.le)
    (Complex.normSq_nonneg _)

/-- A channel whose positive-imaginary normalized slope is nonpositive cannot complete the
universal positive incidence response to the analytic prime--polar--Gamma source.  The latter
requires a positive, nonremovable compensating slope. -/
theorem not_sourceFaithfulCompletion_of_I_mul_div_re_nonpos
    (C : ℂ → ℂ)
    (hpassive : ∀ {eta : ℝ}, 0 < eta →
      (C (Complex.I * eta) / (Complex.I * eta)).re ≤ 0) :
    ¬ ∀ z : ℂ,
      continuedPrimeArchSourceRelativeTrace z =
        mobiusIncidenceUniversalGapResponse z + C z := by
  intro hbridge
  let c : ℂ := deriv continuedPrimeArchSourceRelativeTrace 0
  have hmap_mem : ∀ᶠ eta : ℝ in nhdsWithin 0 (Ioi 0),
      Complex.I * (eta : ℂ) ∈ ({0} : Set ℂ)ᶜ := by
    filter_upwards [self_mem_nhdsWithin] with eta heta
    simp only [mem_compl_iff, mem_singleton_iff]
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast heta.ne')
  have hmap : Tendsto
      (fun eta : ℝ => Complex.I * (eta : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 ({0} : Set ℂ)ᶜ) := by
    have hcont : ContinuousAt (fun eta : ℝ => Complex.I * (eta : ℂ)) 0 := by
      fun_prop
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hmap_mem⟩
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have htraceFinite :=
    _root_.HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero
      analyticAt_continuedPrimeArchSourceRelativeTrace.differentiableAt
      continuedPrimeArchSourceRelativeTrace_zero
  have htraceQuotient : Tendsto
      (fun eta : ℝ =>
        continuedPrimeArchSourceRelativeTrace (Complex.I * eta) /
          (Complex.I * eta))
      (nhdsWithin 0 (Ioi 0)) (nhds c) := by
    simpa only [c, Function.comp_def, sub_zero] using htraceFinite.comp hmap
  have htraceRe : Tendsto
      (fun eta : ℝ =>
        (continuedPrimeArchSourceRelativeTrace (Complex.I * eta) /
          (Complex.I * eta)).re)
      (nhdsWithin 0 (Ioi 0)) (nhds c.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp htraceQuotient
  have hsourceLower : ∀ᶠ eta : ℝ in nhdsWithin 0 (Ioi 0),
      c.re - 1 <
        (continuedPrimeArchSourceRelativeTrace (Complex.I * eta) /
          (Complex.I * eta)).re :=
    htraceRe.eventually (eventually_gt_nhds (by linarith))
  have hgapUpper : ∀ᶠ eta : ℝ in nhdsWithin 0 (Ioi 0),
      (mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
        (Complex.I * eta)).re < c.re - 1 :=
    tendsto_mobiusIncidenceUniversalGapResponse_I_mul_div_re_nhdsGT_zero_atBot
      |>.eventually (eventually_lt_atBot _)
  have hfalse : ∀ᶠ eta : ℝ in nhdsWithin 0 (Ioi 0), False := by
    filter_upwards [self_mem_nhdsWithin, hsourceLower, hgapUpper] with eta heta hsource hgap
    have hresponse := hpassive heta
    have hsum :
        continuedPrimeArchSourceRelativeTrace (Complex.I * eta) /
            (Complex.I * eta) =
          mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
              (Complex.I * eta) +
            C (Complex.I * eta) / (Complex.I * eta) := by
      rw [hbridge (Complex.I * eta)]
      ring
    rw [hsum] at hsource
    simp only [Complex.add_re] at hsource
    linarith
  exact (Filter.Eventually.exists hfalse).elim fun _ h => h

/-- No finite Hermitian KMS entropy-production response can supply the correction from the
universal incidence response to the completed source. -/
theorem not_sourceFaithfulCompletion_by_finiteKMSEntropyProductionResponse
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) :
    ¬ ∀ z : ℂ,
      continuedPrimeArchSourceRelativeTrace z =
        mobiusIncidenceUniversalGapResponse z +
          HTGeometry.finiteTransitionPassiveResponse
            (finiteKMSEntropyProductionTransitionIntensity β energy amplitude)
            energy z := by
  exact not_sourceFaithfulCompletion_of_I_mul_div_re_nonpos _
    (fun heta =>
      finiteKMSEntropyProductionTransitionPassiveResponse_I_mul_div_re_nonpos
        β energy amplitude hHermitian heta)

/-- Nor can a cofinal thermodynamic limit of finite Hermitian entropy-production responses
provide that correction.  A successful source-faithful KMS construction must introduce a signed
channel before the passive scalar response is formed. -/
theorem not_tendsto_finiteKMSEntropyProductionResponse_to_mobiusIncidenceSourceCompletion
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hHermitian : ∀ N a b, amplitude N b a = star (amplitude N a b)) :
    ¬ ∀ z : ℂ, 0 < z.im →
      Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity
          (β N) (energy N) (amplitude N)) (energy N) z)
        atTop (nhds (mobiusIncidenceSourceCompletion z)) := by
  intro hconv
  apply not_sourceFaithfulCompletion_of_I_mul_div_re_nonpos
    mobiusIncidenceSourceCompletion
  · intro eta heta
    have hlim := hconv (Complex.I * eta) (by simp [heta])
    have hquot := hlim.div_const (Complex.I * eta)
    have hre : Tendsto
        (fun N ↦ (HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N)
          (Complex.I * eta) / (Complex.I * eta)).re)
        atTop (nhds (mobiusIncidenceSourceCompletion
          (Complex.I * eta) / (Complex.I * eta)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp hquot
    exact isClosed_Iic.mem_of_tendsto hre
      (Filter.Eventually.of_forall fun N ↦
        finiteKMSEntropyProductionTransitionPassiveResponse_I_mul_div_re_nonpos
          (β N) (energy N) (amplitude N) (hHermitian N) heta)
  · intro z
    unfold mobiusIncidenceSourceCompletion
    ring

end RHTower
