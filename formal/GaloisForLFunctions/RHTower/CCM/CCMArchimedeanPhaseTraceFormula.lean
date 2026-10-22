import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseTraceReduction
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseDerivative
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanRealTraceCocycle
import GaloisForLFunctions.RHTower.StrongTraceClassMultiplierLimit
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import GaloisForLFunctions.HTGeometry.SchwartzPositiveMeasureRepresentation
import GaloisForLFunctions.HTGeometry.SchwartzSpectralMeasureForm

/-!
# Literal CCM archimedean phase trace formula

This file closes the non-formal trace computation in Connes--Consani Proposition 7(iv).  Compact
Schwartz cutoffs of the bounded conjugate Gamma phase satisfy the already-proved real-line trace
cocycle.  They converge strongly, but not in operator norm.  Uniformly bounded strong convergence
against the fixed trace-class quantized differential transports their traces to the literal
unitary phase multiplier.  The exact Gamma phase ODE then gives the source phase-rate integral.

No diagonal-kernel trace rule, phase regularity premise, trace-limit premise, or source proposition
is assumed.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped ENNReal InnerProductSpace Real SchwartzMap Topology

namespace RHTower

/-- Complex conjugate of the literal CCM scattering phase. -/
def ccmArchimedeanScatteringConjPhase (t : ℝ) : ℂ :=
  (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t)

theorem ccmArchimedeanScatteringConjPhase_hasTemperateGrowth :
    Function.HasTemperateGrowth ccmArchimedeanScatteringConjPhase := by
  have h := Complex.conjCLE.hasTemperateGrowth.comp
    ccmArchimedeanScatteringPhase_hasTemperateGrowth
  unfold ccmArchimedeanScatteringConjPhase
  simpa only [Function.comp_def, ccmArchimedeanScatteringConjPhase,
    Complex.conjCLE_apply] using h

@[simp]
theorem norm_ccmArchimedeanScatteringConjPhase (t : ℝ) :
    ‖ccmArchimedeanScatteringConjPhase t‖ = 1 := by
  rw [ccmArchimedeanScatteringConjPhase, Complex.norm_conj,
    norm_ccmArchimedeanScatteringPhase]

/-- Compact Schwartz approximation to the bounded conjugate scattering phase. -/
def ccmArchimedeanScatteringConjCutoff (n : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ ccmArchimedeanScatteringConjPhase
    (SchwartzMap.scaledUnitCutoff n)

@[simp]
theorem ccmArchimedeanScatteringConjCutoff_apply (n : ℕ) (t : ℝ) :
    ccmArchimedeanScatteringConjCutoff n t =
      ccmArchimedeanScatteringConjPhase t *
        SchwartzMap.scaledUnitCutoff n t := by
  rw [ccmArchimedeanScatteringConjCutoff,
    SchwartzMap.smulLeftCLM_apply_apply
      ccmArchimedeanScatteringConjPhase_hasTemperateGrowth]
  exact smul_eq_mul _ _

theorem norm_ccmArchimedeanScatteringConjCutoff_le_one
    (n : ℕ) (t : ℝ) :
    ‖ccmArchimedeanScatteringConjCutoff n t‖ ≤ 1 := by
  rw [ccmArchimedeanScatteringConjCutoff_apply, norm_mul,
    norm_ccmArchimedeanScatteringConjPhase, one_mul]
  exact SchwartzMap.scaledUnitCutoff_norm_le_one n t

/-- Bounded `L²` realization of a compact conjugate-phase cutoff, with the sharp common bound
one built into its construction. -/
def ccmArchimedeanScatteringConjCutoffL2Multiplier (n : ℕ) :
    SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (ccmArchimedeanScatteringConjCutoff n).continuous.measurable
    zero_le_one
    (norm_ccmArchimedeanScatteringConjCutoff_le_one n)

theorem norm_ccmArchimedeanScatteringConjCutoffL2Multiplier_le_one
    (n : ℕ) :
    ‖ccmArchimedeanScatteringConjCutoffL2Multiplier n‖ ≤ 1 :=
  norm_lpBoundedMulCLM_le
    (ccmArchimedeanScatteringConjCutoff n).continuous.measurable
    zero_le_one
    (norm_ccmArchimedeanScatteringConjCutoff_le_one n)

theorem ccmArchimedeanScatteringConjCutoffL2Multiplier_eq_schwartzMultiplier
    (n : ℕ) :
    ccmArchimedeanScatteringConjCutoffL2Multiplier n =
      ccmSchwartzMultiplier (ccmArchimedeanScatteringConjCutoff n) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [
    lpBoundedMulCLM_coeFn
      (ccmArchimedeanScatteringConjCutoff n).continuous.measurable
      zero_le_one
      (norm_ccmArchimedeanScatteringConjCutoff_le_one n) x,
    ccmSchwartzMultiplier_coeFn
      (ccmArchimedeanScatteringConjCutoff n) x]
    with t hleft hright
  exact hleft.trans hright.symm

theorem tendsto_scaledUnitCutoff_apply_one (t : ℝ) :
    Tendsto (fun n : ℕ => SchwartzMap.scaledUnitCutoff n t)
      atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  symm
  apply SchwartzMap.scaledUnitCutoff_apply_of_abs_le
  exact hN.le.trans ((by exact_mod_cast hn : (N : ℝ) ≤ n) |>.trans (by linarith))

theorem tendsto_ccmArchimedeanScatteringConjCutoff_apply
    (t : ℝ) :
    Tendsto (fun n : ℕ => ccmArchimedeanScatteringConjCutoff n t)
      atTop (𝓝 (ccmArchimedeanScatteringConjPhase t)) := by
  simpa only [ccmArchimedeanScatteringConjCutoff_apply, mul_one] using
    (tendsto_const_nhds.mul (tendsto_scaledUnitCutoff_apply_one t))

/-- Compact conjugate-phase multipliers converge strongly to the literal bounded conjugate phase
multiplier.  Operator-norm convergence is neither claimed nor used. -/
theorem tendsto_ccmArchimedeanScatteringConjCutoffL2Multiplier_apply
    (x : SoninL2) :
    Tendsto
      (fun n : ℕ => ccmArchimedeanScatteringConjCutoffL2Multiplier n x)
      atTop (𝓝 (ccmArchimedeanScatteringConjL2Multiplier x)) := by
  have hconjMeas : Measurable ccmArchimedeanScatteringConjPhase :=
    ccmArchimedeanScatteringConjPhase_hasTemperateGrowth.1.continuous.measurable
  have hraw := MeasureTheory.tendsto_lpBoundedMulCLM_apply
    (μ := (volume : Measure ℝ))
    (φ := fun n : ℕ => ccmArchimedeanScatteringConjCutoff n)
    (ψ := ccmArchimedeanScatteringConjPhase)
    (fun n => (ccmArchimedeanScatteringConjCutoff n).continuous.measurable)
    hconjMeas zero_le_one
    norm_ccmArchimedeanScatteringConjCutoff_le_one
    (fun t => by rw [norm_ccmArchimedeanScatteringConjPhase])
    tendsto_ccmArchimedeanScatteringConjCutoff_apply x
  have htarget :
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
          hconjMeas zero_le_one
          (fun t => by rw [norm_ccmArchimedeanScatteringConjPhase]) x =
        ccmArchimedeanScatteringConjL2Multiplier x := by
    apply Lp.ext
    filter_upwards [
      lpBoundedMulCLM_coeFn hconjMeas zero_le_one
        (fun t => by rw [norm_ccmArchimedeanScatteringConjPhase]) x,
      ccmArchimedeanScatteringConjL2Multiplier_ae x]
      with t hleft hright
    rw [hleft, hright, ccmArchimedeanScatteringConjPhase]
    rfl
  rw [← htarget]
  exact hraw

/-- Schwartz multiplication by the complex Gamma phase rate. -/
def ccmGammaHardyPhaseRateMul (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun t : ℝ => (gammaHardyPhaseRate t : ℂ)) g

@[simp]
theorem ccmGammaHardyPhaseRateMul_apply (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ccmGammaHardyPhaseRateMul g t =
      (gammaHardyPhaseRate t : ℂ) * g t := by
  rw [ccmGammaHardyPhaseRateMul,
    SchwartzMap.smulLeftCLM_apply_apply
      gammaHardyPhaseRate_complex_hasTemperateGrowth]
  exact smul_eq_mul _ _

/-- Scalar density left after the conjugate phase is multiplied into the derivative of a
phase-weighted test. -/
def ccmArchimedeanPhaseTraceDensity (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (2 * Complex.I) • ccmGammaHardyPhaseRateMul g +
    SchwartzMap.derivCLM ℂ ℂ g

@[simp]
theorem ccmArchimedeanPhaseTraceDensity_apply
    (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ccmArchimedeanPhaseTraceDensity g t =
      2 * Complex.I * (gammaHardyPhaseRate t : ℂ) * g t +
        deriv (g : ℝ → ℂ) t := by
  simp only [ccmArchimedeanPhaseTraceDensity, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, ccmGammaHardyPhaseRateMul_apply,
    SchwartzMap.derivCLM_apply]
  ring

/-- The integral of a Schwartz derivative on the real line is zero. -/
theorem integral_deriv_schwartz_eq_zero (g : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, deriv (g : ℝ → ℂ) t = 0 := by
  have h := SchwartzMap.fourier_negI_deriv_apply g 0
  rw [SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul] at h
  simp only [mul_zero, Complex.ofReal_zero, Complex.exp_zero, one_smul,
    ofReal_zero, zero_mul] at h
  have hI : (-I) * (∫ t : ℝ, deriv (g : ℝ → ℂ) t) = 0 := by
    change (-I) • (∫ t : ℝ, deriv (g : ℝ → ℂ) t) = 0
    rw [← MeasureTheory.integral_smul]
    simpa only [_root_.smul_apply, smul_eq_mul,
      SchwartzMap.derivCLM_apply] using h
  exact (mul_eq_zero.mp hI).resolve_left (by simp)

theorem integral_ccmArchimedeanPhaseTraceDensity
    (g : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, ccmArchimedeanPhaseTraceDensity g t =
      2 * Complex.I *
        ∫ t : ℝ, (gammaHardyPhaseRate t : ℂ) * g t := by
  change SchwartzMap.integralCLM ℂ (volume : Measure ℝ)
      (ccmArchimedeanPhaseTraceDensity g) = _
  rw [ccmArchimedeanPhaseTraceDensity, map_add, map_smul,
    SchwartzMap.integralCLM_apply]
  have hderiv : ∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ g) x = 0 := by
    simpa only [SchwartzMap.derivCLM_apply] using
      integral_deriv_schwartz_eq_zero g
  rw [SchwartzMap.integralCLM_apply]
  rw [hderiv, add_zero]
  change (2 * I) * (∫ x : ℝ, ccmGammaHardyPhaseRateMul g x) = _
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact ccmGammaHardyPhaseRateMul_apply g t

/-- Every compact cutoff stage is evaluated by the exact Schwartz real-line cocycle. -/
theorem opTrace_ccmArchimedeanScatteringConjCutoff_comp_quantizedDifferential
    (n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace
        (ccmArchimedeanScatteringConjCutoffL2Multiplier n ∘L
          ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g)) =
      (Complex.I / (Real.pi : ℂ)) *
        ∫ t : ℝ, SchwartzMap.scaledUnitCutoff n t *
          ccmArchimedeanPhaseTraceDensity g t := by
  rw [ccmArchimedeanScatteringConjCutoffL2Multiplier_eq_schwartzMultiplier]
  change ContinuousLinearMap.opTrace
      (ccmSchwartzMultiplier (ccmArchimedeanScatteringConjCutoff n) *
        ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g)) = _
  rw [opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_local]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [ccmArchimedeanScatteringConjCutoff_apply,
    ccmArchimedeanScatteringConjPhase,
    ccmArchimedeanPhaseTraceDensity_apply]
  calc
    (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
        SchwartzMap.scaledUnitCutoff n t *
        deriv (ccmArchimedeanScatteringPhaseMul g : ℝ → ℂ) t =
      SchwartzMap.scaledUnitCutoff n t *
        ((starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
          deriv (ccmArchimedeanScatteringPhaseMul g : ℝ → ℂ) t) := by ring
    _ = SchwartzMap.scaledUnitCutoff n t *
        (2 * I * (gammaHardyPhaseRate t : ℂ) * g t +
          deriv (g : ℝ → ℂ) t) := by
      rw [star_mul_deriv_ccmArchimedeanScatteringPhaseMul]

/-- Trace of the literal bounded conjugate phase times the quantized differential of `u g`.
This is the rigorous non-formal core of CCM Proposition 7(iv). -/
theorem opTrace_ccmArchimedeanScatteringConj_comp_quantizedDifferential
    (g : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace
        (ccmArchimedeanScatteringConjL2Multiplier ∘L
          ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g)) =
      (-2 / (Real.pi : ℂ)) *
        ∫ t : ℝ, (gammaHardyPhaseRate t : ℂ) * g t := by
  let T : SoninL2 →L[ℂ] SoninL2 :=
    ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g)
  have hT : T.IsTraceClass :=
    (ccmQuantizedDifferential_memSchattenClass_one
      (ccmArchimedeanScatteringPhaseMul g)).one_isTraceClass
  have hop := opTrace_comp_tendsto_of_strong_tendsto_of_uniform_bound
    (Aι := ccmArchimedeanScatteringConjCutoffL2Multiplier)
    (A := ccmArchimedeanScatteringConjL2Multiplier)
    hT 1 zero_le_one
    (Filter.Eventually.of_forall
      norm_ccmArchimedeanScatteringConjCutoffL2Multiplier_le_one)
    tendsto_ccmArchimedeanScatteringConjCutoffL2Multiplier_apply
  have hint : Tendsto
      (fun n : ℕ => SchwartzMap.integralCLM ℂ (volume : Measure ℝ)
        (SchwartzMap.compactSupportApproximation n
          (ccmArchimedeanPhaseTraceDensity g)))
      atTop
      (𝓝 (SchwartzMap.integralCLM ℂ (volume : Measure ℝ)
        (ccmArchimedeanPhaseTraceDensity g))) :=
    ((SchwartzMap.integralCLM ℂ (volume : Measure ℝ)).continuous.tendsto
      (ccmArchimedeanPhaseTraceDensity g)).comp
        (SchwartzMap.tendsto_compactSupportApproximation
          (ccmArchimedeanPhaseTraceDensity g))
  have hscalarRaw := (tendsto_const_nhds (x := Complex.I / (Real.pi : ℂ))).mul hint
  have hscalar : Tendsto
      (fun n : ℕ => (Complex.I / (Real.pi : ℂ)) *
        ∫ t : ℝ, SchwartzMap.scaledUnitCutoff n t *
          ccmArchimedeanPhaseTraceDensity g t)
      atTop
      (𝓝 ((-2 / (Real.pi : ℂ)) *
        ∫ t : ℝ, (gammaHardyPhaseRate t : ℂ) * g t)) := by
    convert hscalarRaw using 1
    · funext n
      rw [SchwartzMap.integralCLM_apply]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact (SchwartzMap.compactSupportApproximation_apply n
        (ccmArchimedeanPhaseTraceDensity g) t).symm
    · rw [SchwartzMap.integralCLM_apply,
        integral_ccmArchimedeanPhaseTraceDensity]
      have hpi : (Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      field_simp [hpi]
      rw [Complex.I_sq]
      ring
  have hopScalar : Tendsto
      (fun n : ℕ => ContinuousLinearMap.opTrace
        (ccmArchimedeanScatteringConjCutoffL2Multiplier n ∘L T))
      atTop
      (𝓝 ((-2 / (Real.pi : ℂ)) *
        ∫ t : ℝ, (gammaHardyPhaseRate t : ℂ) * g t)) := by
    apply hscalar.congr'
    filter_upwards with n
    exact (opTrace_ccmArchimedeanScatteringConjCutoff_comp_quantizedDifferential
      n g).symm
  exact tendsto_nhds_unique hop hopScalar

/-- **Connes--Consani Proposition 7(iv), literal archimedean trace identity.**  The tested
logarithmic scattering differential has ordinary operator trace equal to the exact Gamma phase-rate
functional. -/
theorem opTrace_ccmSchwartzMultiplier_mul_scatteringLogDifferential_eq_phaseRate
    (g : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace
        (ccmSchwartzMultiplier g * ccmArchimedeanScatteringLogDifferential) =
      (-1 / (Real.pi : ℂ)) *
        ∫ t : ℝ, (gammaHardyPhaseRate t : ℂ) * g t := by
  rw [opTrace_ccmSchwartzMultiplier_mul_scatteringLogDifferential_eq_reduced]
  change (1 / 2 : ℂ) * ContinuousLinearMap.opTrace
      (ccmArchimedeanScatteringConjL2Multiplier ∘L
        ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g)) = _
  rw [opTrace_ccmArchimedeanScatteringConj_comp_quantizedDifferential]
  ring

end RHTower
