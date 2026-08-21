import GaloisForLFunctions.RHTower.FermiMellinObserver
import GaloisForLFunctions.HTGeometry.ProKummerHolonomyCapacity
import GaloisForLFunctions.HTGeometry.MomentMatrixMechanics
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Phase orthogonality and reflected properness of the Fermi–Mellin observer

The characteristic exponent of the Fermi–Mellin law is the completed eta quotient, so a nontrivial
zeta zero makes the corresponding phase orthogonal to the constants.  The same family is an
exponential family in the exponent, so its reflected information work is the secant of a strictly
convex log partition and vanishes only at the critical centre.
-/

open MeasureTheory Set Complex InformationTheory ProbabilityTheory
open scoped ENNReal

namespace RHTower

noncomputable section

/-! ## Complex integrals against the observer law -/

theorem integral_complex_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) (f : ℝ → ℂ) :
    ∫ t : ℝ, f t ∂(fermiMellinMeasure σ)
      = (∫ t : ℝ in Ioi 0, f t * ((fermiMellinDensity σ t : ℝ) : ℂ))
        / ((fermiMellinNormalizer σ : ℝ) : ℂ) := by
  have hZ := fermiMellinNormalizer_pos hσ
  rw [fermiMellinMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_fermiMellinEDensity σ)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [ENNReal.toReal_ofReal (div_nonneg (fermiMellinDensity_pos (σ := σ) ht0).le hZ.le),
    real_smul]
  push_cast
  field_simp

/-- **(PFM.10).**  The characteristic exponent of the observer law is the completed eta quotient. -/
theorem integral_phase_fermiMellinMeasure {σ τ : ℝ} (hσ : 0 < σ)
    (hs1 : (σ : ℂ) + (τ : ℂ) * I ≠ 1) :
    (∫ t : ℝ, Complex.exp ((τ : ℂ) * (Real.log t : ℂ) * I) ∂(fermiMellinMeasure σ))
      = (Complex.Gamma ((σ : ℂ) + (τ : ℂ) * I)
          * (1 - (2 : ℂ) ^ (1 - ((σ : ℂ) + (τ : ℂ) * I)))
          * riemannZeta ((σ : ℂ) + (τ : ℂ) * I))
        / ((fermiMellinNormalizer σ : ℝ) : ℂ) := by
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hs
  have hsre : 0 < s.re := by simp [hs, hσ]
  rw [integral_complex_fermiMellinMeasure hσ]
  congr 1
  rw [← mellin_salemFermiKernel_eq_closedForm hsre hs1, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have hcpow : (t : ℂ) ^ (s - 1)
      = ((t ^ (σ - 1) : ℝ) : ℂ) * Complex.exp ((τ : ℂ) * (Real.log t : ℂ) * I) := by
    rw [show s - 1 = ((σ : ℂ) - 1) + (τ : ℂ) * I by rw [hs]; ring,
      Complex.cpow_add _ _ (by exact_mod_cast ht0.ne'), cpow_ofReal_sub_one ht0.le]
    congr 1
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht0.ne'), ← Complex.ofReal_log ht0.le]
    congr 1
    ring
  rw [smul_eq_mul, hcpow, salemFermiKernel, fermiMellinDensity]
  push_cast
  ring

/-- **(PFM.12).**  Every nontrivial zeta zero gives exact phase orthogonality in the observer
law. -/
theorem integral_phase_fermiMellinMeasure_eq_zero {σ τ : ℝ} (hσ : 0 < σ)
    (hs1 : (σ : ℂ) + (τ : ℂ) * I ≠ 1) (hzero : riemannZeta ((σ : ℂ) + (τ : ℂ) * I) = 0) :
    (∫ t : ℝ, Complex.exp ((τ : ℂ) * (Real.log t : ℂ) * I) ∂(fermiMellinMeasure σ)) = 0 := by
  rw [integral_phase_fermiMellinMeasure hσ hs1, hzero, mul_zero, zero_div]

/-! ## The quantum Fisher lower bound -/

theorem norm_one_sub_exp_mul_I_le (x : ℝ) : ‖1 - Complex.exp ((x : ℂ) * I)‖ ≤ |x| := by
  have hsq := GaloisForLFunctions.HTGeometry.norm_one_sub_exp_sq x
  have hsin : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
    have h := Real.abs_sin_le_abs (x := x / 2)
    nlinarith [abs_nonneg (Real.sin (x / 2)), abs_nonneg (x / 2),
      sq_abs (Real.sin (x / 2)), sq_abs (x / 2)]
  have h4 : ‖1 - Complex.exp ((x : ℂ) * I)‖ ^ 2 ≤ x ^ 2 := by
    rw [hsq]
    nlinarith [hsin]
  nlinarith [norm_nonneg (1 - Complex.exp ((x : ℂ) * I)), abs_nonneg x, sq_abs x]

theorem integral_log_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) :
    ∫ t : ℝ, Real.log t ∂(fermiMellinMeasure σ) = fermiLogMean σ := by
  have h := integral_log_pow_fermiMellinMeasure hσ 1
  rw [fermiLogMean, fermiLogMoment_zero, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show Real.log t = Real.log t ^ 1
  rw [pow_one]

theorem integral_centered_sq_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) :
    ∫ t : ℝ, (Real.log t - fermiLogMean σ) ^ 2 ∂(fermiMellinMeasure σ) = fermiLogVariance σ := by
  rw [integral_fermiMellinMeasure hσ, fermiLogVariance_eq_div hσ, fermiLogMoment_zero]

theorem integrable_centered_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ => Real.log t - fermiLogMean σ) (fermiMellinMeasure σ) := by
  haveI := fermiMellinMeasure_isProbabilityMeasure hσ
  have h1 := integrable_log_pow_fermiMellinMeasure hσ 1
  have h1' : Integrable (fun t : ℝ => Real.log t) (fermiMellinMeasure σ) :=
    h1.congr (Filter.Eventually.of_forall fun t => by
      show Real.log t ^ 1 = Real.log t
      rw [pow_one])
  exact h1'.sub (integrable_const _)

theorem integrable_centered_sq_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ => (Real.log t - fermiLogMean σ) ^ 2) (fermiMellinMeasure σ) := by
  haveI := fermiMellinMeasure_isProbabilityMeasure hσ
  have h2 := integrable_log_pow_fermiMellinMeasure hσ 2
  have h1 := integrable_log_pow_fermiMellinMeasure hσ 1
  have h0 : Integrable (fun _ : ℝ => (1 : ℝ)) (fermiMellinMeasure σ) := integrable_const _
  have hcomb := (h2.sub (h1.const_mul (2 * fermiLogMean σ))).add
    (h0.const_mul (fermiLogMean σ ^ 2))
  refine hcomb.congr (Filter.Eventually.of_forall fun t => ?_)
  show Real.log t ^ 2 - 2 * fermiLogMean σ * Real.log t ^ 1
      + fermiLogMean σ ^ 2 * 1 = (Real.log t - fermiLogMean σ) ^ 2
  ring

/-- **(PFM.14).**  At a nontrivial zeta zero the logarithmic variance of the observer law is at
least the inverse square of the ordinate; equivalently the pure-state quantum Fisher information of
the induced phase orbit is at least `4 τ⁻²`. -/
theorem one_le_sq_mul_fermiLogVariance_of_zetaZero {σ τ : ℝ} (hσ : 0 < σ)
    (hs1 : (σ : ℂ) + (τ : ℂ) * I ≠ 1) (hzero : riemannZeta ((σ : ℂ) + (τ : ℂ) * I) = 0) :
    1 ≤ τ ^ 2 * fermiLogVariance σ := by
  haveI := fermiMellinMeasure_isProbabilityMeasure hσ
  set m : ℝ := fermiLogMean σ with hm
  set μ := fermiMellinMeasure σ with hμ
  have hphase := integral_phase_fermiMellinMeasure_eq_zero hσ hs1 hzero
  have hbdd : ∀ t : ℝ, ‖Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I)‖ = 1 := by
    intro t
    rw [show (τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I
        = (((τ * (Real.log t - m) : ℝ)) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hmeasexp : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I)) μ := by
    refine Measurable.aestronglyMeasurable ?_
    exact Complex.measurable_exp.comp
      ((measurable_const.mul (Complex.measurable_ofReal.comp
        (Real.measurable_log.sub measurable_const))).mul measurable_const)
  have hexpint : Integrable
      (fun t : ℝ => Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I)) μ :=
    Integrable.mono' (integrable_const (1 : ℝ)) hmeasexp
      (Filter.Eventually.of_forall fun t => le_of_eq (hbdd t))
  have hint : Integrable (fun t : ℝ =>
      1 - Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I)) μ :=
    (integrable_const (1 : ℂ)).sub hexpint
  have hshift : (∫ t : ℝ, Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I) ∂μ) = 0 := by
    have hfac : ∀ t : ℝ, Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I)
        = Complex.exp (-((τ : ℂ) * (m : ℂ) * I))
          * Complex.exp ((τ : ℂ) * (Real.log t : ℂ) * I) := by
      intro t
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hfac), integral_const_mul, hphase,
      mul_zero]
  have hone : (∫ t : ℝ, (1 - Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I)) ∂μ) = 1 := by
    rw [integral_sub (integrable_const (1 : ℂ)) hexpint, hshift, sub_zero, integral_const]
    simp
  have hle1 : (1 : ℝ) ≤ ∫ t : ℝ, |τ * (Real.log t - m)| ∂μ := by
    have hnorm : ‖(∫ t : ℝ, (1 - Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I)) ∂μ)‖
        ≤ ∫ t : ℝ, ‖1 - Complex.exp ((τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) * I)‖ ∂μ :=
      norm_integral_le_integral_norm _
    rw [hone, norm_one] at hnorm
    refine le_trans hnorm ?_
    refine integral_mono hint.norm ?_ (fun t => ?_)
    · exact ((integrable_centered_fermiMellinMeasure hσ).const_mul τ).abs
    · have := norm_one_sub_exp_mul_I_le (τ * (Real.log t - m))
      rw [show ((τ * (Real.log t - m) : ℝ) : ℂ)
          = (τ : ℂ) * ((Real.log t - m : ℝ) : ℂ) by push_cast; ring] at this
      exact this
  have hcs : (∫ t : ℝ, |Real.log t - m| ∂μ) ≤ Real.sqrt (fermiLogVariance σ) := by
    have hg1 : AEStronglyMeasurable (fun _ : ℝ => (1 : ℂ)) μ := aestronglyMeasurable_const
    have hg2 : AEStronglyMeasurable (fun t : ℝ => ((Real.log t - m : ℝ) : ℂ)) μ :=
      Measurable.aestronglyMeasurable
        (Complex.measurable_ofReal.comp (Real.measurable_log.sub measurable_const))
    have h1 : Integrable (fun t : ℝ => ‖(1 : ℂ)‖ ^ 2) μ := integrable_const _
    have h2 : Integrable (fun t : ℝ => ‖((Real.log t - m : ℝ) : ℂ)‖ ^ 2) μ := by
      refine (integrable_centered_sq_fermiMellinMeasure hσ).congr
        (Filter.Eventually.of_forall fun t => ?_)
      show (Real.log t - fermiLogMean σ) ^ 2 = ‖((Real.log t - m : ℝ) : ℂ)‖ ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hm]
    have hCS := GaloisForLFunctions.HTGeometry.integral_mul_le_sqrt_mul_sqrt_measure
      (μ := μ) hg1 hg2 h1 h2
    simp only [norm_one, one_mul, Complex.norm_real, Real.norm_eq_abs, one_pow] at hCS
    rw [integral_const, probReal_univ] at hCS
    simp only [smul_eq_mul, mul_one, Real.sqrt_one, one_mul] at hCS
    refine le_trans hCS (le_of_eq ?_)
    congr 1
    rw [← integral_centered_sq_fermiMellinMeasure hσ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show |Real.log t - m| ^ 2 = (Real.log t - fermiLogMean σ) ^ 2
    rw [sq_abs, hm]
  have habs : (∫ t : ℝ, |τ * (Real.log t - m)| ∂μ) = |τ| * ∫ t : ℝ, |Real.log t - m| ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show |τ * (Real.log t - m)| = |τ| * |Real.log t - m|
    rw [abs_mul]
  rw [habs] at hle1
  have hvar := (fermiLogVariance_pos hσ).le
  have hsq : Real.sqrt (fermiLogVariance σ) ^ 2 = fermiLogVariance σ := Real.sq_sqrt hvar
  have hsqrt_nonneg : 0 ≤ Real.sqrt (fermiLogVariance σ) := Real.sqrt_nonneg _
  have hstep : (1 : ℝ) ≤ |τ| * Real.sqrt (fermiLogVariance σ) := by
    refine le_trans hle1 ?_
    exact mul_le_mul_of_nonneg_left hcs (abs_nonneg τ)
  nlinarith [hstep, hsq, hsqrt_nonneg, abs_nonneg τ, sq_abs τ]

/-! ## The quantum Fisher identity -/

theorem momentNormalizedVariance_fermiLogMoment (σ : ℝ) :
    HTGeometry.momentNormalizedVariance (fermiLogMoment σ) Polynomial.X = fermiLogVariance σ := by
  rw [HTGeometry.momentNormalizedVariance, HTGeometry.momentNormalizedExpectation,
    HTGeometry.momentNormalizedExpectation, fermiLogVariance, fermiLogMean]
  congr 2
  · simp [HTGeometry.momentFunctional, Polynomial.X_pow_eq_monomial,
      Polynomial.sum_monomial_index]
  · simp [HTGeometry.momentFunctional, Polynomial.sum_X_index]

/-- **(PFM.13).**  The pure-state quantum Fisher information of the logarithmic phase orbit is four
times the logarithmic variance of the observer law. -/
theorem pureStateQuantumFisher_fermiMellin {σ : ℝ} (hσ : 0 < σ) :
    HTGeometry.pureStateQuantumFisherValue (fermiLogMoment σ 0)
        (HTGeometry.momentFunctional (fermiLogMoment σ) Polynomial.X)
        (HTGeometry.momentFunctional (fermiLogMoment σ) (Polynomial.X ^ 2))
      = 4 * fermiLogVariance σ := by
  have h0 : fermiLogMoment σ 0 ≠ 0 := by
    rw [fermiLogMoment_zero]
    exact (fermiMellinNormalizer_pos hσ).ne'
  rw [HTGeometry.pureStateQuantumFisherValue_moment_eq_four_mul_normalizedVariance
    (fermiLogMoment σ) h0 Polynomial.X, momentNormalizedVariance_fermiLogMoment σ]

/-! ## Reflected information properness -/

/-- The observer family is an exponential family in the exponent. -/
theorem fermiMellinMeasure_tilted {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fermiMellinMeasure b).tilted (fun t : ℝ => (a - b) * Real.log t) = fermiMellinMeasure a := by
  have hZa := fermiMellinNormalizer_pos ha
  have hZb := fermiMellinNormalizer_pos hb
  have hmgf : (∫ t : ℝ, Real.exp ((a - b) * Real.log t) ∂(fermiMellinMeasure b))
      = fermiMellinNormalizer a / fermiMellinNormalizer b := by
    have h := mgf_log_fermiMellin hb (a - b)
    rw [mgf] at h
    rw [h]
    congr 2
    ring
  have hdens : Measurable fun t : ℝ =>
      ENNReal.ofReal (Real.exp ((a - b) * Real.log t)
        / (fermiMellinNormalizer a / fermiMellinNormalizer b)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.div_const ?_ _)
    exact Real.measurable_exp.comp (Real.measurable_log.const_mul _)
  rw [Measure.tilted, hmgf, fermiMellinMeasure, fermiMellinMeasure,
    ← withDensity_mul _ (measurable_fermiMellinEDensity b) hdens]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul
    (div_nonneg (fermiMellinDensity_pos (σ := b) ht0).le hZb.le)]
  congr 1
  rw [div_mul_div_comm, mul_comm (fermiMellinDensity b t),
    exp_mul_log_mul_density (σ := b) (u := a - b) ht0, show b + (a - b) = a by ring]
  field_simp

/-- **(PFM.17).**  The reflected likelihood ratio depends only on the sufficient scale. -/
theorem llr_fermiMellinMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    llr (fermiMellinMeasure a) (fermiMellinMeasure b) =ᵐ[fermiMellinMeasure b]
      fun t : ℝ => (a - b) * Real.log t - (fermiLogPartition a - fermiLogPartition b) := by
  haveI := fermiMellinMeasure_isProbabilityMeasure hb
  have hZa := fermiMellinNormalizer_pos ha
  have hZb := fermiMellinNormalizer_pos hb
  have hint : Integrable (fun t : ℝ => Real.exp ((a - b) * Real.log t))
      (fermiMellinMeasure b) := by
    have := integrable_exp_mul_log hb (u := a - b) (by linarith)
    exact this
  have hlog := log_rnDeriv_tilted_left_self (μ := fermiMellinMeasure b)
    (f := fun t : ℝ => (a - b) * Real.log t) hint
  rw [fermiMellinMeasure_tilted ha hb] at hlog
  have hmgf : (∫ t : ℝ, Real.exp ((a - b) * Real.log t) ∂(fermiMellinMeasure b))
      = fermiMellinNormalizer a / fermiMellinNormalizer b := by
    have h := mgf_log_fermiMellin hb (a - b)
    rw [mgf] at h
    rw [h]
    congr 2
    ring
  rw [hmgf, Real.log_div hZa.ne' hZb.ne'] at hlog
  filter_upwards [hlog] with t htv
  show Real.log (((fermiMellinMeasure a).rnDeriv (fermiMellinMeasure b)) t).toReal
    = (a - b) * Real.log t - (fermiLogPartition a - fermiLogPartition b)
  rw [htv, fermiLogPartition, fermiLogPartition]

/-- **(PFM.18), directed cost.** -/
theorem toReal_klDiv_fermiMellinMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (klDiv (fermiMellinMeasure a) (fermiMellinMeasure b)).toReal
      = (a - b) * fermiLogMean a - (fermiLogPartition a - fermiLogPartition b) := by
  haveI := fermiMellinMeasure_isProbabilityMeasure ha
  haveI := fermiMellinMeasure_isProbabilityMeasure hb
  have hint : Integrable (fun t : ℝ => Real.exp ((a - b) * Real.log t))
      (fermiMellinMeasure b) := integrable_exp_mul_log hb (u := a - b) (by linarith)
  have hac : fermiMellinMeasure a ≪ fermiMellinMeasure b := by
    rw [← fermiMellinMeasure_tilted ha hb]
    exact tilted_absolutelyContinuous _ _
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  rw [integral_congr_ae (hac.ae_le (llr_fermiMellinMeasure ha hb))]
  have hlogint : Integrable (fun t : ℝ => Real.log t) (fermiMellinMeasure a) := by
    have h1 := integrable_log_pow_fermiMellinMeasure ha 1
    exact h1.congr (Filter.Eventually.of_forall fun t => by
      show Real.log t ^ 1 = Real.log t
      rw [pow_one])
  rw [integral_sub ((hlogint.const_mul (a - b))) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_log_fermiMellinMeasure ha]

/-- **(PFM.18).**  Symmetric reflected work is the secant increment of the first response. -/
theorem jeffreys_fermiMellinMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (klDiv (fermiMellinMeasure a) (fermiMellinMeasure b)).toReal
        + (klDiv (fermiMellinMeasure b) (fermiMellinMeasure a)).toReal
      = (a - b) * (fermiLogMean a - fermiLogMean b) := by
  rw [toReal_klDiv_fermiMellinMeasure ha hb, toReal_klDiv_fermiMellinMeasure hb ha]
  ring

theorem fermiLogMean_strictMonoOn : StrictMonoOn fermiLogMean (Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fermiLogVariance)
    (convex_Ioi (0 : ℝ)) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_fermiLogMean (hx : (0:ℝ) < x)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_fermiLogMean
      (interior_subset hx : x ∈ Ioi (0:ℝ))).hasDerivWithinAt
  · intro x hx
    exact fermiLogVariance_pos (interior_subset hx : x ∈ Ioi (0:ℝ))

/-- **(PFM.19).**  Every off-centre reflected formation pays strictly positive information work. -/
theorem jeffreys_fermiMellinMeasure_eq_zero_iff_center {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (klDiv (fermiMellinMeasure σ) (fermiMellinMeasure (1 - σ))).toReal
        + (klDiv (fermiMellinMeasure (1 - σ)) (fermiMellinMeasure σ)).toReal = 0
      ↔ σ = 1 / 2 := by
  have hr : 0 < 1 - σ := by linarith
  rw [jeffreys_fermiMellinMeasure h0 hr]
  constructor
  · intro hzero
    rcases lt_trichotomy σ (1 - σ) with hlt | heq | hgt
    · have hmono := fermiLogMean_strictMonoOn (a := σ) h0 (b := 1 - σ) hr hlt
      nlinarith [hzero, hmono, hlt]
    · linarith
    · have hmono := fermiLogMean_strictMonoOn (a := 1 - σ) hr (b := σ) h0 hgt
      nlinarith [hzero, hmono, hgt]
  · intro hc
    subst hc
    norm_num

end

end RHTower
