import GaloisForLFunctions.RHTower.HasseSondowRowMellin
import GaloisForLFunctions.HTGeometry.HasseModularCocycle
import GaloisForLFunctions.HTGeometry.WeightedHolder

/-!
# The Fermi–Mellin observer law

The scale marginal of the Hasse packet is the positive Fermi–Mellin law on the half line.  Its
characteristic exponent is the completed eta quotient, so every nontrivial zeta zero gives an exact
orthogonality relation, and the quantum Fisher information of the induced phase orbit is bounded
below by the inverse square of the ordinate.
-/

open MeasureTheory Set Complex

namespace RHTower

noncomputable section

/-- The unnormalized Fermi–Mellin density (PFM.6). -/
def fermiMellinDensity (σ t : ℝ) : ℝ := t ^ (σ - 1) * (Real.exp t + 1)⁻¹

theorem fermiMellinDensity_pos {σ t : ℝ} (ht : 0 < t) : 0 < fermiMellinDensity σ t := by
  have h1 : (0 : ℝ) < t ^ (σ - 1) := Real.rpow_pos_of_pos ht _
  have h2 : (0 : ℝ) < Real.exp t + 1 := by positivity
  rw [fermiMellinDensity]
  positivity

theorem integrableOn_fermiMellinDensity {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fermiMellinDensity σ) (Ioi 0) := by
  have hre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have h := integrableOn_rpow_mul_fermi hre
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  rw [fermiMellinDensity]
  congr 2

/-- The Fermi–Mellin normalizer (PFM.15). -/
def fermiMellinNormalizer (σ : ℝ) : ℝ := ∫ t : ℝ in Ioi 0, fermiMellinDensity σ t

theorem fermiMellinNormalizer_pos {σ : ℝ} (hσ : 0 < σ) : 0 < fermiMellinNormalizer σ := by
  rw [fermiMellinNormalizer,
    integral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_fermiMellinDensity hσ)]
  · have hsupp : (volume.restrict (Ioi 0)) (Function.support (fermiMellinDensity σ)) ≠ 0 := by
      intro hzero
      have hsub : Ioi (0 : ℝ) ⊆ Function.support (fermiMellinDensity σ) := by
        intro t ht
        exact (fermiMellinDensity_pos (σ := σ) ht).ne'
      have hle := measure_mono (μ := volume.restrict (Ioi 0)) hsub
      rw [Measure.restrict_apply_self] at hle
      rw [hzero] at hle
      simp [Real.volume_Ioi] at hle
    exact pos_iff_ne_zero.2 hsupp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (fermiMellinDensity_pos (σ := σ) ht).le

/-- The normalizer is the Mellin transform of the Fermi kernel, hence `Γ(σ)·η(σ)`. -/
theorem ofReal_fermiMellinNormalizer (σ : ℝ) :
    ((fermiMellinNormalizer σ : ℝ) : ℂ) = mellin salemFermiKernel (σ : ℂ) := by
  rw [fermiMellinNormalizer, mellin, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [fermiMellinDensity, Complex.ofReal_mul, smul_eq_mul, cpow_ofReal_sub_one ht0.le]
  congr 1
  rw [salemFermiKernel, ← Complex.ofReal_inv]

theorem fermiMellinNormalizer_eq_gamma_mul_eta {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    ((fermiMellinNormalizer σ : ℝ) : ℂ)
      = Complex.Gamma (σ : ℂ) * (1 - (2 : ℂ) ^ (1 - (σ : ℂ))) * riemannZeta (σ : ℂ) := by
  rw [ofReal_fermiMellinNormalizer σ]
  refine mellin_salemFermiKernel_eq_closedForm (by simpa using hσ) ?_
  intro h
  exact hσ1 (by exact_mod_cast h)

/-- The normalized Fermi–Mellin observer law (PFM.6). -/
def fermiMellinMeasure (σ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t =>
    ENNReal.ofReal (fermiMellinDensity σ t / fermiMellinNormalizer σ)

theorem measurable_fermiMellinDensity (σ : ℝ) : Measurable (fermiMellinDensity σ) := by
  have hrw : fermiMellinDensity σ = fun t : ℝ => t ^ (σ - 1) * (Real.exp t + 1)⁻¹ := rfl
  rw [hrw]
  fun_prop

theorem measurable_fermiMellinEDensity (σ : ℝ) :
    Measurable (fun t : ℝ => ENNReal.ofReal (fermiMellinDensity σ t / fermiMellinNormalizer σ)) :=
  ENNReal.measurable_ofReal.comp
    ((measurable_fermiMellinDensity σ).div_const (fermiMellinNormalizer σ))

theorem integral_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) (f : ℝ → ℝ) :
    ∫ t : ℝ, f t ∂(fermiMellinMeasure σ)
      = (∫ t : ℝ in Ioi 0, f t * fermiMellinDensity σ t) / fermiMellinNormalizer σ := by
  have hZ := fermiMellinNormalizer_pos hσ
  rw [fermiMellinMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_fermiMellinEDensity σ)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [smul_eq_mul,
    ENNReal.toReal_ofReal (div_nonneg (fermiMellinDensity_pos (σ := σ) ht0).le hZ.le)]
  ring

theorem integrable_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun t : ℝ => f t * fermiMellinDensity σ t) (Ioi 0)) :
    Integrable f (fermiMellinMeasure σ) := by
  have hZ := fermiMellinNormalizer_pos hσ
  rw [fermiMellinMeasure,
    integrable_withDensity_iff_integrable_smul₀' (measurable_fermiMellinEDensity σ).aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine IntegrableOn.congr_fun (hf.div_const (fermiMellinNormalizer σ)) (fun t ht => ?_)
    measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  show f t * fermiMellinDensity σ t / fermiMellinNormalizer σ
    = (ENNReal.ofReal (fermiMellinDensity σ t / fermiMellinNormalizer σ)).toReal • f t
  rw [ENNReal.toReal_ofReal (div_nonneg (fermiMellinDensity_pos (σ := σ) ht0).le hZ.le),
    smul_eq_mul]
  ring

theorem fermiMellinMeasure_isProbabilityMeasure {σ : ℝ} (hσ : 0 < σ) :
    IsProbabilityMeasure (fermiMellinMeasure σ) := by
  constructor
  have hZ := fermiMellinNormalizer_pos hσ
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi 0)]
      fun t => fermiMellinDensity σ t / fermiMellinNormalizer σ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (fermiMellinDensity_pos (σ := σ) ht).le hZ.le
  rw [fermiMellinMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_fermiMellinDensity hσ).div_const (fermiMellinNormalizer σ)) hnn,
    integral_div]
  rw [show (∫ t : ℝ in Ioi 0, fermiMellinDensity σ t) = fermiMellinNormalizer σ from rfl,
    div_self hZ.ne', ENNReal.ofReal_one]

/-! ## The log-moment exponential family -/

open ProbabilityTheory

/-- The `n`-th logarithmic moment of the unnormalized Fermi–Mellin density. -/
def fermiLogMoment (σ : ℝ) (n : ℕ) : ℝ :=
  ∫ t : ℝ in Ioi 0, (Real.log t) ^ n * fermiMellinDensity σ t

theorem fermiLogMoment_zero (σ : ℝ) : fermiLogMoment σ 0 = fermiMellinNormalizer σ := by
  rw [fermiLogMoment, fermiMellinNormalizer]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [pow_zero, one_mul]

theorem exp_mul_log_mul_density {σ u t : ℝ} (ht : 0 < t) :
    Real.exp (u * Real.log t) * fermiMellinDensity σ t = fermiMellinDensity (σ + u) t := by
  rw [fermiMellinDensity, fermiMellinDensity,
    show u * Real.log t = Real.log t * u by ring, ← Real.rpow_def_of_pos ht,
    ← mul_assoc, ← Real.rpow_add ht]
  congr 2
  ring

theorem integrable_exp_mul_log {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < σ + u) :
    Integrable (fun t : ℝ => Real.exp (u * Real.log t)) (fermiMellinMeasure σ) := by
  refine integrable_fermiMellinMeasure hσ ?_
  refine IntegrableOn.congr_fun (integrableOn_fermiMellinDensity hu) (fun t ht => ?_)
    measurableSet_Ioi
  exact (exp_mul_log_mul_density (σ := σ) (u := u) ht).symm

theorem Ioi_subset_integrableExpSet {σ : ℝ} (hσ : 0 < σ) :
    Ioi (-σ) ⊆ integrableExpSet Real.log (fermiMellinMeasure σ) := by
  intro u hu
  have hu' : -σ < u := hu
  exact integrable_exp_mul_log hσ (by linarith)

theorem zero_mem_interior_integrableExpSet {σ : ℝ} (hσ : 0 < σ) :
    (0 : ℝ) ∈ interior (integrableExpSet Real.log (fermiMellinMeasure σ)) := by
  refine interior_maximal (Ioi_subset_integrableExpSet hσ) isOpen_Ioi ?_
  simpa using hσ

theorem mem_interior_integrableExpSet {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < σ + u) :
    u ∈ interior (integrableExpSet Real.log (fermiMellinMeasure σ)) := by
  refine interior_maximal (Ioi_subset_integrableExpSet hσ) isOpen_Ioi ?_
  simpa using by linarith

/-- Every logarithmic moment is finite in the Fermi–Mellin law. -/
theorem integrable_log_pow_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Integrable (fun t : ℝ => (Real.log t) ^ n) (fermiMellinMeasure σ) :=
  integrable_pow_of_mem_interior_integrableExpSet (zero_mem_interior_integrableExpSet hσ) n

theorem integrableOn_log_pow_mul_fermiMellinDensity {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (Real.log t) ^ n * fermiMellinDensity σ t) (Ioi 0) := by
  have hZ := fermiMellinNormalizer_pos hσ
  have h := integrable_log_pow_fermiMellinMeasure hσ n
  rw [fermiMellinMeasure,
    integrable_withDensity_iff_integrable_smul₀' (measurable_fermiMellinEDensity σ).aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  have hmul := h.mul_const (fermiMellinNormalizer σ)
  refine IntegrableOn.congr_fun hmul (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  show (ENNReal.ofReal (fermiMellinDensity σ t / fermiMellinNormalizer σ)).toReal •
      (Real.log t) ^ n * fermiMellinNormalizer σ
    = (Real.log t) ^ n * fermiMellinDensity σ t
  rw [ENNReal.toReal_ofReal (div_nonneg (fermiMellinDensity_pos (σ := σ) ht).le hZ.le),
    smul_eq_mul]
  field_simp

theorem integral_log_pow_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∫ t : ℝ, (Real.log t) ^ n ∂(fermiMellinMeasure σ)
      = fermiLogMoment σ n / fermiMellinNormalizer σ := by
  rw [integral_fermiMellinMeasure hσ, fermiLogMoment]

/-! ## The response chain of the log-partition -/

theorem integral_log_pow_mul_exp_fermiMellinMeasure {σ : ℝ} (hσ : 0 < σ) (u : ℝ)
    (n : ℕ) :
    (∫ t : ℝ, (Real.log t) ^ n * Real.exp (u * Real.log t) ∂(fermiMellinMeasure σ))
      = fermiLogMoment (σ + u) n / fermiMellinNormalizer σ := by
  rw [integral_fermiMellinMeasure hσ, fermiLogMoment]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [mul_assoc, exp_mul_log_mul_density (σ := σ) (u := u) ht0]

theorem mgf_log_fermiMellin {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    mgf Real.log (fermiMellinMeasure σ) u
      = fermiMellinNormalizer (σ + u) / fermiMellinNormalizer σ := by
  have h := integral_log_pow_mul_exp_fermiMellinMeasure hσ u 0
  rw [fermiLogMoment_zero] at h
  rw [mgf, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show Real.exp (u * Real.log t) = Real.log t ^ 0 * Real.exp (u * Real.log t)
  rw [pow_zero, one_mul]

theorem iteratedDeriv_mgf_log_fermiMellin {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < σ + u) (n : ℕ) :
    iteratedDeriv n (mgf Real.log (fermiMellinMeasure σ)) u
      = fermiLogMoment (σ + u) n / fermiMellinNormalizer σ := by
  rw [iteratedDeriv_mgf (mem_interior_integrableExpSet hσ hu) n]
  exact integral_log_pow_mul_exp_fermiMellinMeasure hσ u n

theorem hasDerivAt_shift {g : ℝ → ℝ} {a c : ℝ} (h : HasDerivAt (fun u : ℝ => g (a + u)) c 0) :
    HasDerivAt g c a := by
  have hsub : HasDerivAt (fun b : ℝ => b - a) 1 a := by
    simpa using (hasDerivAt_id a).sub_const a
  have hcomp : HasDerivAt ((fun u : ℝ => g (a + u)) ∘ fun b : ℝ => b - a) (c * 1) a := by
    have h0 : HasDerivAt (fun u : ℝ => g (a + u)) c (a - a) := by
      simpa using h
    exact HasDerivAt.comp a h0 hsub
  have hfun : ((fun u : ℝ => g (a + u)) ∘ fun b : ℝ => b - a) = g := by
    funext b
    show g (a + (b - a)) = g b
    congr 1
    ring
  rw [hfun, mul_one] at hcomp
  exact hcomp

/-- **(PFM.16), response chain.**  Differentiating a logarithmic moment raises its order. -/
theorem hasDerivAt_fermiLogMoment {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    HasDerivAt (fun a : ℝ => fermiLogMoment a n) (fermiLogMoment σ (n + 1)) σ := by
  have hZ := fermiMellinNormalizer_pos hσ
  have hmem := zero_mem_interior_integrableExpSet hσ
  have hbase := hasDerivAt_iteratedDeriv_mgf hmem n
  rw [integral_log_pow_mul_exp_fermiMellinMeasure hσ 0 (n + 1)] at hbase
  have hev : (fun u : ℝ => iteratedDeriv n (mgf Real.log (fermiMellinMeasure σ)) u)
      =ᶠ[nhds (0 : ℝ)] fun u : ℝ => fermiLogMoment (σ + u) n / fermiMellinNormalizer σ := by
    filter_upwards [(isOpen_Ioi (a := -σ)).mem_nhds (by simpa using hσ)] with u hu
    have hu' : -σ < u := hu
    exact iteratedDeriv_mgf_log_fermiMellin hσ (by linarith) n
  have hshift : HasDerivAt (fun u : ℝ => fermiLogMoment (σ + u) n / fermiMellinNormalizer σ)
      (fermiLogMoment (σ + 0) (n + 1) / fermiMellinNormalizer σ) 0 :=
    hbase.congr_of_eventuallyEq hev.symm
  rw [add_zero] at hshift
  have hmul := hshift.mul_const (fermiMellinNormalizer σ)
  rw [div_mul_cancel₀ _ hZ.ne'] at hmul
  refine hasDerivAt_shift ?_
  refine hmul.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · rfl
  · filter_upwards with u
    rw [div_mul_cancel₀ _ hZ.ne']

/-- The log partition of the Fermi–Mellin family (PFM.15). -/
def fermiLogPartition (σ : ℝ) : ℝ := Real.log (fermiMellinNormalizer σ)

/-- The mean of the logarithmic scale statistic. -/
def fermiLogMean (σ : ℝ) : ℝ := fermiLogMoment σ 1 / fermiLogMoment σ 0

/-- The variance of the logarithmic scale statistic. -/
def fermiLogVariance (σ : ℝ) : ℝ :=
  fermiLogMoment σ 2 / fermiLogMoment σ 0 - fermiLogMean σ ^ 2

/-- **(PFM.16), first response.** -/
theorem hasDerivAt_fermiLogPartition {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt fermiLogPartition (fermiLogMean σ) σ := by
  have hZ := fermiMellinNormalizer_pos hσ
  have h0 := hasDerivAt_fermiLogMoment hσ 0
  have hpos : 0 < fermiLogMoment σ 0 := by rw [fermiLogMoment_zero]; exact hZ
  have hlog := h0.log (ne_of_gt hpos)
  have hfun : (fun a : ℝ => Real.log (fermiLogMoment a 0)) = fermiLogPartition := by
    funext a
    rw [fermiLogPartition, fermiLogMoment_zero]
  rw [hfun] at hlog
  exact hlog.congr_deriv (by rw [fermiLogMean])

/-- **(PFM.16), second response.** -/
theorem hasDerivAt_fermiLogMean {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt fermiLogMean (fermiLogVariance σ) σ := by
  have hZ := fermiMellinNormalizer_pos hσ
  have hpos : 0 < fermiLogMoment σ 0 := by rw [fermiLogMoment_zero]; exact hZ
  have h1 := hasDerivAt_fermiLogMoment hσ 1
  have h0 := hasDerivAt_fermiLogMoment hσ 0
  have hdiv := h1.div h0 (ne_of_gt hpos)
  refine hdiv.congr_deriv ?_
  rw [fermiLogVariance, fermiLogMean]
  field_simp

/-! ## Strict convexity -/

theorem integral_centered_sq_fermi {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ in Ioi 0, (Real.log t - fermiLogMean σ) ^ 2 * fermiMellinDensity σ t)
      = fermiLogMoment σ 2 - 2 * fermiLogMean σ * fermiLogMoment σ 1
        + fermiLogMean σ ^ 2 * fermiLogMoment σ 0 := by
  have h2 := integrableOn_log_pow_mul_fermiMellinDensity hσ 2
  have h1 := integrableOn_log_pow_mul_fermiMellinDensity hσ 1
  have h0 := integrableOn_log_pow_mul_fermiMellinDensity hσ 0
  rw [show (∫ t : ℝ in Ioi 0, (Real.log t - fermiLogMean σ) ^ 2 * fermiMellinDensity σ t)
      = ∫ t : ℝ in Ioi 0, ((Real.log t) ^ 2 * fermiMellinDensity σ t
        - 2 * fermiLogMean σ * ((Real.log t) ^ 1 * fermiMellinDensity σ t)
        + fermiLogMean σ ^ 2 * ((Real.log t) ^ 0 * fermiMellinDensity σ t)) from
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by ring]
  have hB : IntegrableOn (fun t : ℝ =>
      fermiLogMean σ ^ 2 * ((Real.log t) ^ 0 * fermiMellinDensity σ t)) (Ioi 0) :=
    h0.const_mul _
  have hC : IntegrableOn (fun t : ℝ =>
      2 * fermiLogMean σ * ((Real.log t) ^ 1 * fermiMellinDensity σ t)) (Ioi 0) :=
    h1.const_mul _
  have hA : IntegrableOn (fun t : ℝ => (Real.log t) ^ 2 * fermiMellinDensity σ t
      - 2 * fermiLogMean σ * ((Real.log t) ^ 1 * fermiMellinDensity σ t)) (Ioi 0) := h2.sub hC
  rw [MeasureTheory.integral_add hA hB, MeasureTheory.integral_sub h2 hC,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rfl

theorem fermiLogVariance_eq_div {σ : ℝ} (hσ : 0 < σ) :
    fermiLogVariance σ
      = (∫ t : ℝ in Ioi 0, (Real.log t - fermiLogMean σ) ^ 2 * fermiMellinDensity σ t)
        / fermiLogMoment σ 0 := by
  have hpos : 0 < fermiLogMoment σ 0 := by
    rw [fermiLogMoment_zero]
    exact fermiMellinNormalizer_pos hσ
  rw [integral_centered_sq_fermi hσ, fermiLogVariance, fermiLogMean]
  field_simp
  ring

/-- **(PFM.16), strict convexity.**  The logarithmic scale is not almost surely constant, so the
second response of the log partition is strictly positive. -/
theorem fermiLogVariance_pos {σ : ℝ} (hσ : 0 < σ) : 0 < fermiLogVariance σ := by
  have hpos : 0 < fermiLogMoment σ 0 := by
    rw [fermiLogMoment_zero]
    exact fermiMellinNormalizer_pos hσ
  have hint := by
    have h2 := integrableOn_log_pow_mul_fermiMellinDensity hσ 2
    have h1 := integrableOn_log_pow_mul_fermiMellinDensity hσ 1
    have h0 := integrableOn_log_pow_mul_fermiMellinDensity hσ 0
    have hcomb := (h2.sub (h1.const_mul (2 * fermiLogMean σ))).add
      (h0.const_mul (fermiLogMean σ ^ 2))
    exact IntegrableOn.congr_fun hcomb (fun t ht => by
      show (Real.log t) ^ 2 * fermiMellinDensity σ t
          - 2 * fermiLogMean σ * ((Real.log t) ^ 1 * fermiMellinDensity σ t)
          + fermiLogMean σ ^ 2 * ((Real.log t) ^ 0 * fermiMellinDensity σ t)
        = (Real.log t - fermiLogMean σ) ^ 2 * fermiMellinDensity σ t
      ring) measurableSet_Ioi
  have hnn : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
      0 ≤ (Real.log t - fermiLogMean σ) ^ 2 * fermiMellinDensity σ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (sq_nonneg _) (fermiMellinDensity_pos (σ := σ) ht).le
  have hintpos : 0 < ∫ t : ℝ in Ioi 0,
      (Real.log t - fermiLogMean σ) ^ 2 * fermiMellinDensity σ t := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    set c : ℝ := Real.exp (fermiLogMean σ) with hc
    have hc0 : 0 < c := Real.exp_pos _
    have hsub : Ioo c (c + 1) ⊆ Function.support
        (fun t : ℝ => (Real.log t - fermiLogMean σ) ^ 2 * fermiMellinDensity σ t) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans hc0 ht.1
      have hlog : fermiLogMean σ < Real.log t := by
        have hlt := Real.log_lt_log hc0 ht.1
        rwa [hc, Real.log_exp] at hlt
      exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (fermiMellinDensity_pos (σ := σ) ht0).ne'
    have hval : (volume.restrict (Ioi (0 : ℝ))) (Ioo c (c + 1)) = 1 := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      have hinter : Ioo c (c + 1) ∩ Ioi (0 : ℝ) = Ioo c (c + 1) :=
        Set.inter_eq_left.2 fun x hx => lt_trans hc0 hx.1
      rw [hinter, Real.volume_Ioo]
      norm_num
    have hmeas := measure_mono (μ := volume.restrict (Ioi (0 : ℝ))) hsub
    rw [hval] at hmeas
    exact lt_of_lt_of_le zero_lt_one hmeas
  rw [fermiLogVariance_eq_div hσ]
  exact div_pos hintpos hpos

end

end RHTower
