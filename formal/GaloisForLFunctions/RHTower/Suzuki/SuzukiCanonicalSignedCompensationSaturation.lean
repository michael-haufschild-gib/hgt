import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreAlignedGammaCompletion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyReporterSecantTransitionCoreEscape
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarDLVPRate
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszSuzukiGreenProducerClassification
import GaloisForLFunctions.RHTower.PrimeVacuumErrorTransfer

/-!
# Canonical signed compensation saturates the Suzuki transition core

The positive transition core cannot enter the rectangular Ward criterion without a signed
linear-scale correction.  This module proves that the literal coefficient-faithful completion
already has exactly that scale.

The analytic input is the unconditional de la Vallée Poussin decay of the polar-normalized
Chebyshev error.  A dominated-convergence argument shows that unit-rate causal resolution
preserves this relative decay.  Consequently the completed Suzuki amplitude is negligible
relative to its divergent atomic amplitude.  Compensating amplitudes before squaring therefore
removes asymptotically all transition-core energy.

The capstone gives the exact `n / 576` lower admission forced by the earlier Ward rigidity theorem
on apertures `8n`.  What remains after correction is definitionally the aligned completed energy,
whose eventual boundedness is equivalent to RH.  No RH premise, numerical computation, or added
axiom is used.
-/

open Filter Set MeasureTheory Topology
open scoped Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

def criticalMellinPolarNormalizedError (h : ℝ) : ℝ :=
  Real.exp (-h / 2) * criticalMellinNormalizedChebyshevError h

theorem measurable_criticalMellinPolarNormalizedError :
    Measurable criticalMellinPolarNormalizedError := by
  exact (Real.measurable_exp.comp
    ((measurable_id.neg.div_const 2))).mul
      measurable_criticalMellinNormalizedChebyshevError

theorem criticalMellinPolarNormalizedError_eq_neg_one_of_nonpos
    {h : ℝ} (hh : h ≤ 0) :
    criticalMellinPolarNormalizedError h = -1 := by
  have hexp_le : Real.exp h ≤ 1 := by simpa using Real.exp_le_one_iff.mpr hh
  have hpsiReal : chebyshevPsiReal (Real.exp h) = 0 := by
    have hle := chebyshevPsiReal_mono hexp_le
    have hnonneg := chebyshevPsiReal_nonneg (Real.exp h)
    have hone : chebyshevPsiReal 1 = 0 :=
      chebyshevPsiReal_eq_zero_of_lt_two le_rfl (by norm_num)
    rw [hone] at hle
    linarith
  have hpsi : Chebyshev.psi (Real.exp h) = 0 := by
    rw [← chebyshevPsiReal_eq_psi]
    exact hpsiReal
  have hsqrt : Real.sqrt (Real.exp h) = Real.exp (h / 2) := by
    rw [← Real.exp_half]
  rw [criticalMellinPolarNormalizedError,
    criticalMellinNormalizedChebyshevError, criticalMellinError,
    criticalCumulative_vonMangoldt_eq_psi, hpsi, hsqrt]
  have hne : Real.exp (h / 2) ≠ 0 := Real.exp_ne_zero _
  field_simp [hne]
  rw [zero_sub, mul_neg, ← Real.exp_add]
  congr 1
  ring

theorem tendsto_criticalMellinPolarNormalizedError_atTop_zero :
    Tendsto criticalMellinPolarNormalizedError atTop (𝓝 0) := by
  exact tendsto_exp_neg_half_mul_criticalMellinNormalizedChebyshevError_atTop_zero

theorem exists_global_bound_criticalMellinPolarNormalizedError :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℝ,
      |criticalMellinPolarNormalizedError h| ≤ M := by
  have hlim := tendsto_criticalMellinPolarNormalizedError_atTop_zero
  have hlo : ∀ᶠ h : ℝ in atTop, -1 < criticalMellinPolarNormalizedError h :=
    (tendsto_order.1 hlim).1 (-1) (by norm_num)
  have hhi : ∀ᶠ h : ℝ in atTop, criticalMellinPolarNormalizedError h < 1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  obtain ⟨H, hH⟩ :=
    (hlo.and (hhi.and (eventually_ge_atTop (0 : ℝ)))).exists_forall_of_atTop
  let M : ℝ := 2 * H + 1
  have hM1 : 1 ≤ M := by
    have := (hH H le_rfl).2.2
    dsimp only [M]
    linarith
  refine ⟨M, by linarith, fun h => ?_⟩
  by_cases hhH : H ≤ h
  · have hh := hH h hhH
    rw [abs_le]
    constructor <;> linarith
  · by_cases hh0 : h ≤ 0
    · rw [criticalMellinPolarNormalizedError_eq_neg_one_of_nonpos hh0,
        abs_neg, abs_one]
      exact hM1
    · have hhpos : 0 ≤ h := le_of_not_ge hh0
      have herr := abs_criticalMellinNormalizedChebyshevError_le_log_sqrt hhpos
      have hq : |criticalMellinPolarNormalizedError h| ≤ 2 * h + 1 := by
        rw [criticalMellinPolarNormalizedError, abs_mul,
          abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-h / 2) * |criticalMellinNormalizedChebyshevError h| ≤
              Real.exp (-h / 2) * ((2 * h + 1) * Real.exp (h / 2)) :=
            mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le
          _ = 2 * h + 1 := by
            rw [show Real.exp (-h / 2) * ((2 * h + 1) * Real.exp (h / 2)) =
                (2 * h + 1) * (Real.exp (-h / 2) * Real.exp (h / 2)) by ring,
              ← Real.exp_add]
            rw [show -h / 2 + h / 2 = 0 by ring, Real.exp_zero, mul_one]
      dsimp only [M]
      linarith

theorem tendsto_integral_exp_three_halves_mul_polarNormalizedError_atTop_zero :
    Tendsto (fun h : ℝ =>
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-3 * t / 2) * criticalMellinPolarNormalizedError (h - t))
      atTop (𝓝 0) := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_global_bound_criticalMellinPolarNormalizedError
  have hdom : IntegrableOn (fun t : ℝ => M * Real.exp (-3 * t / 2)) (Ioi 0) := by
    have hi := (exp_neg_integrableOn_Ioi 0
      (b := (3 / 2 : ℝ)) (by norm_num)).const_mul M
    change Integrable (fun t : ℝ => M * Real.exp (-3 * t / 2))
      (volume.restrict (Ioi 0))
    convert hi using 1
    funext t
    congr 2
    ring
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun h t =>
      Real.exp (-3 * t / 2) * criticalMellinPolarNormalizedError (h - t))
    (f := fun _t => (0 : ℝ))
    (bound := fun t => M * Real.exp (-3 * t / 2))
    (Eventually.of_forall fun h => by
      have hexpMeas : Measurable (fun t : ℝ => Real.exp (-3 * t / 2)) := by
        fun_prop
      have hqMeas : Measurable
          (fun t : ℝ => criticalMellinPolarNormalizedError (h - t)) :=
        measurable_criticalMellinPolarNormalizedError.comp (by fun_prop)
      exact (hexpMeas.mul hqMeas).aestronglyMeasurable)
    (Eventually.of_forall fun h => by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-3 * t / 2) *
              |criticalMellinPolarNormalizedError (h - t)| ≤
            Real.exp (-3 * t / 2) * M :=
          mul_le_mul_of_nonneg_left (hbound (h - t)) (Real.exp_pos _).le
        _ = M * Real.exp (-3 * t / 2) := by ring)
    hdom
    (Eventually.of_forall fun t => by
      have hshift : Tendsto (fun h : ℝ => h - t) atTop atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right atTop (-t) tendsto_id)
      have hq :=
        tendsto_criticalMellinPolarNormalizedError_atTop_zero.comp hshift
      simpa using hq.const_mul (Real.exp (-3 * t / 2)))
  simpa using hdct

theorem exp_neg_half_mul_criticalMellinChebyshevResolventSource_eq
    (h : ℝ) :
    Real.exp (-h / 2) * criticalMellinChebyshevResolventSource h =
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-3 * t / 2) * criticalMellinPolarNormalizedError (h - t) := by
  rw [criticalMellinChebyshevResolventSource,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [criticalMellinPolarNormalizedError,
    ← criticalMellinNormalizedChebyshevError_eq_apertureError]
  have hexp : Real.exp (-h / 2) * Real.exp (-t) =
      Real.exp (-3 * t / 2) * Real.exp (-(h - t) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-h / 2) *
        (Real.exp (-t) * criticalMellinNormalizedChebyshevError (h - t)) =
      (Real.exp (-h / 2) * Real.exp (-t)) *
        criticalMellinNormalizedChebyshevError (h - t) := by ring
    _ = (Real.exp (-3 * t / 2) * Real.exp (-(h - t) / 2)) *
        criticalMellinNormalizedChebyshevError (h - t) := by rw [hexp]
    _ = Real.exp (-3 * t / 2) *
        (Real.exp (-(h - t) / 2) *
          criticalMellinNormalizedChebyshevError (h - t)) := by ring

theorem tendsto_exp_neg_half_mul_criticalMellinChebyshevResolventSource_atTop_zero :
    Tendsto (fun h : ℝ => Real.exp (-h / 2) *
      criticalMellinChebyshevResolventSource h) atTop (𝓝 0) := by
  apply tendsto_integral_exp_three_halves_mul_polarNormalizedError_atTop_zero.congr'
  filter_upwards with h
  exact (exp_neg_half_mul_criticalMellinChebyshevResolventSource_eq h).symm

private theorem tendsto_log_natCast_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_sqrt_natCast_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_bounded_div_sqrt_natCast_zero
    {f : ℕ → ℝ} {K : ℝ} (hf : ∀ᶠ N : ℕ in atTop, |f N| ≤ K) :
    Tendsto (fun N : ℕ => f N / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun N : ℕ => K / Real.sqrt (N : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_sqrt_natCast_atTop
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hf, tendsto_sqrt_natCast_atTop.eventually_gt_atTop 0] with N hfN hsqrt
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hsqrt]
  exact div_le_div_of_nonneg_right hfN hsqrt.le

theorem tendsto_unitRieszCoherentCompletedOutgoingCharge_div_sqrt_atTop_zero :
    Tendsto (fun N : ℕ => unitRieszCoherentCompletedOutgoingCharge N /
      Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  have hres :=
    tendsto_exp_neg_half_mul_criticalMellinChebyshevResolventSource_atTop_zero.comp
      tendsto_log_natCast_atTop
  have hhalf : Tendsto (fun N : ℕ => (1 / 2 : ℝ) *
      (Real.exp (-Real.log (N : ℝ) / 2) *
        criticalMellinChebyshevResolventSource (Real.log (N : ℝ))))
      atTop (𝓝 0) := by
    simpa using hres.const_mul (1 / 2 : ℝ)
  refine hhalf.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (Real.log (N : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN, hsqrt]
  simp only [div_eq_mul_inv]
  rw [← Real.exp_neg]
  ring

theorem tendsto_unitRieszCoherentPrimeOutgoingCharge_div_sqrt_atTop_one_third :
    Tendsto (fun N : ℕ => unitRieszCoherentPrimeOutgoingCharge N /
      Real.sqrt (N : ℝ)) atTop (𝓝 (1 / 3 : ℝ)) := by
  have hcompleted :=
    tendsto_unitRieszCoherentCompletedOutgoingCharge_div_sqrt_atTop_zero
  have hadd := hcompleted.add_const (1 / 3 : ℝ)
  simpa only [zero_add] using hadd.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by positivity
    rw [unitRieszCoherentCompletedOutgoingCharge,
      unitRieszCoherentPolarOutgoingCharge_eq]
    field_simp
    ring)

theorem tendsto_unitRieszSuzukiPolarCorrection_logNat_div_sqrt_atTop_zero :
    Tendsto (fun N : ℕ => unitRieszSuzukiPolarCorrection (Real.log (N : ℝ)) /
      Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  apply tendsto_bounded_div_sqrt_natCast_zero
  filter_upwards [tendsto_log_natCast_atTop.eventually_ge_atTop unitRieszSuzukiBase]
    with N hN
  exact abs_unitRieszSuzukiPolarCorrection_le hN

theorem tendsto_unitRieszSuzukiArchCorrection_logNat_div_sqrt_atTop_zero :
    Tendsto (fun N : ℕ => unitRieszSuzukiArchCorrection (Real.log (N : ℝ)) /
      Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  apply tendsto_bounded_div_sqrt_natCast_zero
  filter_upwards [tendsto_log_natCast_atTop.eventually_ge_atTop unitRieszSuzukiBase]
    with N hN
  exact abs_unitRieszSuzukiArchCorrection_le hN

theorem tendsto_unitRieszSuzukiGreen_logNat_div_sqrt_atTop_zero :
    Tendsto (fun N : ℕ => unitRieszSuzukiGreen (Real.log (N : ℝ)) /
      Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  have hout :=
    tendsto_unitRieszCoherentCompletedOutgoingCharge_div_sqrt_atTop_zero
  have hpolar :=
    tendsto_unitRieszSuzukiPolarCorrection_logNat_div_sqrt_atTop_zero
  have harch :=
    tendsto_unitRieszSuzukiArchCorrection_logNat_div_sqrt_atTop_zero
  have hlim := hout.sub hpolar |>.add harch
  simpa only [sub_zero, zero_add] using hlim.congr' (by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    rw [unitRieszSuzuki_outgoing_eq_green hN]
    ring)

theorem tendsto_suzukiNaturalApertureCompletedLowerHardyAmplitude_div_sqrt_atTop_zero :
    Tendsto (fun N : ℕ => suzukiNaturalApertureCompletedLowerHardyAmplitude N /
      Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  apply tendsto_unitRieszSuzukiGreen_logNat_div_sqrt_atTop_zero.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hgreen :=
    suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_green (N - 2)
  have hgreen' : suzukiNaturalApertureCompletedLowerHardyAmplitude N =
      unitRieszSuzukiGreen (Real.log (N : ℝ)) := by
    simpa [Nat.sub_add_cancel hN] using hgreen
  rw [hgreen']

theorem tendsto_suzukiCompletedAmplitude_div_primeOutgoingCharge_atTop_zero :
    Tendsto (fun N : ℕ =>
      suzukiNaturalApertureCompletedLowerHardyAmplitude N /
        unitRieszCoherentPrimeOutgoingCharge N) atTop (𝓝 0) := by
  have hnum :=
    tendsto_suzukiNaturalApertureCompletedLowerHardyAmplitude_div_sqrt_atTop_zero
  have hden :=
    tendsto_unitRieszCoherentPrimeOutgoingCharge_div_sqrt_atTop_one_third
  have hquot := hnum.div hden (by norm_num : (1 / 3 : ℝ) ≠ 0)
  simpa only [zero_div] using hquot.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero] with N hN hA
    have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by positivity
    change
      (suzukiNaturalApertureCompletedLowerHardyAmplitude N / Real.sqrt (N : ℝ)) /
          (unitRieszCoherentPrimeOutgoingCharge N / Real.sqrt (N : ℝ)) =
        suzukiNaturalApertureCompletedLowerHardyAmplitude N /
          unitRieszCoherentPrimeOutgoingCharge N
    field_simp)

/-- The coefficient-faithful signed correction: compensate the atomic and regular-screw
amplitudes before taking the aligned transition-core square. -/
def suzukiTransitionCoreCanonicalSignedCorrection (N : ℕ) : ℝ :=
  suzukiNaturalApertureTransitionCoreCauchyEnergy N -
    suzukiTransitionCoreAlignedGammaCompletedEnergy N

theorem eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero :
    ∀ᶠ N : ℕ in atTop,
      suzukiNaturalApertureTransitionCoreCauchyEnergy N ≠ 0 := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero] with N hN hA hcore
  have hle := unitRieszCoherentPrimeOutgoingCharge_sq_le_transitionCore hN
  rw [hcore] at hle
  nlinarith [sq_pos_of_ne_zero hA]

theorem eventually_suzukiAlignedEnergy_div_transitionCore_eq_completedRatio_sq :
    ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreAlignedGammaCompletedEnergy N /
          suzukiNaturalApertureTransitionCoreCauchyEnergy N =
        (suzukiNaturalApertureCompletedLowerHardyAmplitude N /
          unitRieszCoherentPrimeOutgoingCharge N) ^ 2 := by
  filter_upwards [eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero,
    eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero]
      with N hA hcore
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy, dif_neg hA]
  field_simp

theorem tendsto_suzukiAlignedEnergy_div_transitionCore_atTop_zero :
    Tendsto (fun N : ℕ =>
      suzukiTransitionCoreAlignedGammaCompletedEnergy N /
        suzukiNaturalApertureTransitionCoreCauchyEnergy N) atTop (𝓝 0) := by
  have hsq := tendsto_suzukiCompletedAmplitude_div_primeOutgoingCharge_atTop_zero.pow 2
  simpa using hsq.congr'
    (Filter.EventuallyEq.symm
      eventually_suzukiAlignedEnergy_div_transitionCore_eq_completedRatio_sq)

theorem tendsto_suzukiTransitionCoreCanonicalSignedCorrection_div_core_atTop_one :
    Tendsto (fun N : ℕ =>
      suzukiTransitionCoreCanonicalSignedCorrection N /
        suzukiNaturalApertureTransitionCoreCauchyEnergy N) atTop (𝓝 1) := by
  have hone : Tendsto (fun _N : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hsub := hone.sub
    tendsto_suzukiAlignedEnergy_div_transitionCore_atTop_zero
  simpa only [sub_zero] using hsub.congr' (by
    filter_upwards [eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero]
      with N hcore
    rw [suzukiTransitionCoreCanonicalSignedCorrection]
    field_simp)

/-- Exact admission threshold forced by transition-core Ward semiboundedness.  The canonical
signed correction supplies it unconditionally. -/
theorem eventually_linear_le_suzukiTransitionCoreCanonicalSignedCorrection_eight_mul :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 576 ≤
      suzukiTransitionCoreCanonicalSignedCorrection (8 * n) := by
  have hhalf : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) < suzukiTransitionCoreCanonicalSignedCorrection N /
        suzukiNaturalApertureTransitionCoreCauchyEnergy N :=
    (tendsto_order.1
      tendsto_suzukiTransitionCoreCanonicalSignedCorrection_div_core_atTop_one).1
        (1 / 2) (by norm_num)
  have hscale : Tendsto (fun n : ℕ => 8 * n) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hhalfEight := hscale.eventually hhalf
  filter_upwards [hhalfEight,
    eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ge_linear,
    eventually_ge_atTop (1 : ℕ)] with n hratio hcore hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcorepos : 0 < suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (n : ℝ) / 288) hcore
  have hcorr : (1 / 2 : ℝ) *
      suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) <
        suzukiTransitionCoreCanonicalSignedCorrection (8 * n) :=
    (lt_div_iff₀ hcorepos).mp hratio
  nlinarith

theorem suzukiTransitionCore_sub_canonicalSignedCorrection_eq_alignedEnergy
    (N : ℕ) :
    suzukiNaturalApertureTransitionCoreCauchyEnergy N -
        suzukiTransitionCoreCanonicalSignedCorrection N =
      suzukiTransitionCoreAlignedGammaCompletedEnergy N := by
  rw [suzukiTransitionCoreCanonicalSignedCorrection]
  ring

def SuzukiCanonicalSignedCorrectedTransitionCoreEventuallyBounded : Prop :=
  ∃ B : ℝ, ∀ᶠ N : ℕ in atTop,
    suzukiNaturalApertureTransitionCoreCauchyEnergy N -
      suzukiTransitionCoreCanonicalSignedCorrection N ≤ B

/-- The signed correction discharges the scaling admission, and the residual it leaves is exactly
the existing RH-equivalent aligned completed energy. -/
theorem riemannHypothesis_iff_suzukiCanonicalSignedCorrectedTransitionCoreEventuallyBounded :
    RiemannHypothesis ↔
      SuzukiCanonicalSignedCorrectedTransitionCoreEventuallyBounded := by
  rw [riemannHypothesis_iff_suzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded]
  unfold SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded
    SuzukiCanonicalSignedCorrectedTransitionCoreEventuallyBounded
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, hB.mono fun N hN => ?_⟩
    rwa [suzukiTransitionCore_sub_canonicalSignedCorrection_eq_alignedEnergy]
  · rintro ⟨B, hB⟩
    refine ⟨B, hB.mono fun N hN => ?_⟩
    rwa [suzukiTransitionCore_sub_canonicalSignedCorrection_eq_alignedEnergy] at hN

end


end GaloisForLFunctions.RHTower
