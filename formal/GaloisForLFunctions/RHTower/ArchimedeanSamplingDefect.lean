import GaloisForLFunctions.HTGeometry.SamplingDefectTotalVariation
import GaloisForLFunctions.RHTower.SeamArchimedeanSamplingQuotient
import GaloisForLFunctions.RHTower.XiThetaCriticalTrace
import GaloisForLFunctions.RHTower.XiThetaExplicitBounds

/-!
# The archimedean theta measure is maximally invisible to prime-power sampling

The general order-zero theorem of `HTGeometry/SamplingDefectTotalVariation.lean` is instantiated at
the actual completed-zeta objects.

* `thetaMeasure` — the positive archimedean theta measure `dμ₊ = w_θ(u) du` on `(0,∞)`, with
  `w_θ(u) = e^{u/4}(evenKernel 0 e^u − 1)` the corpus's `archimedeanThetaDensity`; it is finite
  because the corpus's `xiThetaPositiveSource` is integrable, and absolutely continuous by
  construction;
* `primePowerLogs` — the sample sites `{log n : n a prime power}`; countable, and **closed**
  because only finitely many prime powers have logarithm in any bounded interval;
* `isLUB_thetaSamplingPairings` — equation `(4)`: the defect of prime-power sampling is exactly the
  full theta mass;
* `thetaMass_eq_completedRiemannZeta₀` — that mass is the central completed trace
  `Λ₀(1/2)`, via the corpus's critical-trace identity at frequency zero;
* `thetaMass_ge` — equation `(5)`: the explicit bound `2e^{−2π} log 2 ≤ M_θ`, with no numerical
  approximation, from the corpus's `two_exp_le_evenKernel_zero_sub_one`;
* `thetaMeasureCompleted_real_univ`, `isLUB_thetaCompletedSamplingPairings`,
  `normalized_thetaCompleted_defect` — equations `(6)`–`(7)`: completion doubles the absolute defect
  and leaves the normalized defect at its maximal value one.
-/

noncomputable section

open MeasureTheory Set Filter Topology FourierTransform

namespace RHTower.ArchimedeanSampling

open RHTower HurwitzZeta GaloisForLFunctions.HTGeometry.SamplingDefect

/-- The positive-half archimedean theta density, extended by zero. -/
def thetaDensity (u : ℝ) : ℝ := (Set.Ioi (0 : ℝ)).indicator archimedeanThetaDensity u

theorem thetaDensity_nonneg (u : ℝ) : 0 ≤ thetaDensity u := by
  rw [thetaDensity]
  by_cases hu : u ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hu]
    exact (archimedeanThetaDensity_pos u).le
  · rw [Set.indicator_of_notMem hu]

theorem thetaDensity_eq_re (u : ℝ) : thetaDensity u = (xiThetaPositiveSource u).re := by
  rw [thetaDensity, xiThetaPositiveSource]
  by_cases hu : u ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu,
      archimedeanThetaDensity_eq_re_logSource hu]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, Complex.zero_re]

theorem integrable_thetaDensity : Integrable thetaDensity := by
  have h := xiThetaPositiveSource_integrable.re
  exact h.congr (Filter.Eventually.of_forall (fun u => (thetaDensity_eq_re u).symm))

/-- The positive archimedean theta measure. -/
def thetaMeasure : Measure ℝ := volume.withDensity (fun u => ENNReal.ofReal (thetaDensity u))

instance : IsFiniteMeasure thetaMeasure := by
  refine ⟨?_⟩
  rw [thetaMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    MeasureTheory.Measure.restrict_univ]
  have hfin := integrable_thetaDensity.hasFiniteIntegral
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall thetaDensity_nonneg)] at hfin
  exact hfin

theorem thetaMeasure_real_univ : thetaMeasure.real Set.univ = ∫ u, thetaDensity u := by
  rw [MeasureTheory.measureReal_def, thetaMeasure,
    MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall thetaDensity_nonneg)
    integrable_thetaDensity.aestronglyMeasurable]

/-- Absolutely continuous measures annihilate countable sets. -/
theorem thetaMeasure_countable {S : Set ℝ} (hS : S.Countable) : thetaMeasure S = 0 := by
  rw [thetaMeasure, MeasureTheory.withDensity_apply _ hS.measurableSet]
  have hzero : (volume.restrict S) = 0 :=
    MeasureTheory.Measure.restrict_eq_zero.mpr (hS.measure_zero volume)
  rw [hzero]
  exact MeasureTheory.lintegral_zero_measure _

/-! ## The prime-power sample set -/

/-- The logarithms of the prime powers: the archimedean sample sites of the explicit formula. -/
def primePowerLogs : Set ℝ := {u : ℝ | ∃ n : ℕ, IsPrimePow n ∧ u = Real.log n}

theorem primePowerLogs_countable : primePowerLogs.Countable := by
  have hsub : primePowerLogs ⊆ (fun n : ℕ => Real.log n) '' Set.univ := by
    rintro u ⟨n, _, rfl⟩
    exact ⟨n, Set.mem_univ n, rfl⟩
  exact Set.Countable.mono hsub (Set.countable_univ.image _)

theorem finite_primePowerLogs_inter_Icc (a b : ℝ) :
    (primePowerLogs ∩ Set.Icc a b).Finite := by
  have hsub : primePowerLogs ∩ Set.Icc a b
      ⊆ (fun n : ℕ => Real.log n) '' {n : ℕ | n ≤ ⌈Real.exp b⌉₊} := by
    rintro u ⟨⟨n, hpp, rfl⟩, -, hub⟩
    refine ⟨n, ?_, rfl⟩
    have hn2 : 2 ≤ n := hpp.two_le
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hle : (n : ℝ) ≤ Real.exp b := by
      have hexp := Real.exp_le_exp.mpr hub
      rwa [Real.exp_log hnpos] at hexp
    have hceil : (n : ℝ) ≤ (⌈Real.exp b⌉₊ : ℝ) := le_trans hle (Nat.le_ceil _)
    exact_mod_cast hceil
  exact Set.Finite.subset ((Set.finite_Iic (⌈Real.exp b⌉₊)).image _) hsub

theorem isClosed_primePowerLogs : IsClosed primePowerLogs := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  set B : Set ℝ := primePowerLogs ∩ Set.Icc (x - 1) (x + 1) with hB
  have hBfin : B.Finite := finite_primePowerLogs_inter_Icc (x - 1) (x + 1)
  refine ⟨Bᶜ ∩ Set.Ioo (x - 1) (x + 1), ?_, ?_, ?_⟩
  · intro u hu
    intro hupp
    refine hu.1 ?_
    exact ⟨hupp, ⟨le_of_lt hu.2.1, le_of_lt hu.2.2⟩⟩
  · exact (hBfin.isClosed.isOpen_compl).inter isOpen_Ioo
  · refine ⟨?_, ?_, ?_⟩
    · intro hxB
      exact hx hxB.1
    · linarith
    · linarith

theorem thetaMeasure_primePowerLogs : thetaMeasure primePowerLogs = 0 :=
  thetaMeasure_countable primePowerLogs_countable

/-- **Equation (4).**  Prime-power sampling of the positive archimedean theta measure has defect
exactly its full mass: the order-zero information lost is everything. -/
theorem isLUB_thetaSamplingPairings :
    IsLUB (samplingPairings thetaMeasure primePowerLogs) (thetaMeasure.real Set.univ) :=
  isLUB_samplingPairings thetaMeasure isClosed_primePowerLogs thetaMeasure_primePowerLogs

/-! ## The explicit positive lower bound -/

theorem thetaDensity_ge_on_first_block {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) (Real.log 2)) :
    2 * Real.exp (-(2 * Real.pi)) ≤ thetaDensity u := by
  obtain ⟨hu0, hu2⟩ := hu
  have hmem : u ∈ Set.Ioi (0 : ℝ) := hu0
  rw [thetaDensity, Set.indicator_of_mem hmem, archimedeanThetaDensity]
  have hexpu : Real.exp u ≤ 2 := by
    have := Real.exp_le_exp.mpr hu2
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hker := two_exp_le_evenKernel_zero_sub_one (Real.exp_pos u)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexpmono : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-Real.pi * Real.exp u) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hquarter : (1 : ℝ) ≤ Real.exp (u / 4) := by
    refine Real.one_le_exp ?_
    linarith
  have hkerpos : (0 : ℝ) ≤ evenKernel 0 (Real.exp u) - 1 := by
    have := evenKernel_zero_sub_one_pos (Real.exp_pos u)
    linarith
  calc 2 * Real.exp (-(2 * Real.pi))
      ≤ 2 * Real.exp (-Real.pi * Real.exp u) := by linarith
    _ ≤ evenKernel 0 (Real.exp u) - 1 := hker
    _ ≤ Real.exp (u / 4) * (evenKernel 0 (Real.exp u) - 1) := by nlinarith

/-- **Equation (5).**  The lost mass admits an explicit positive lower bound with no numerical
approximation. -/
theorem thetaMass_ge :
    2 * Real.exp (-(2 * Real.pi)) * Real.log 2 ≤ thetaMeasure.real Set.univ := by
  rw [thetaMeasure_real_univ]
  have hblock : (2 * Real.exp (-(2 * Real.pi))) * Real.log 2
      ≤ ∫ u in Set.Ioc (0 : ℝ) (Real.log 2), thetaDensity u := by
    have hconst : ∫ _u in Set.Ioc (0 : ℝ) (Real.log 2), (2 * Real.exp (-(2 * Real.pi)))
        = (Real.log 2) * (2 * Real.exp (-(2 * Real.pi))) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
        Real.volume_Ioc, ENNReal.toReal_ofReal (by
          have hl : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          linarith)]
      ring
    have hmono : ∫ _u in Set.Ioc (0 : ℝ) (Real.log 2), (2 * Real.exp (-(2 * Real.pi)))
        ≤ ∫ u in Set.Ioc (0 : ℝ) (Real.log 2), thetaDensity u := by
      refine MeasureTheory.setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne)
        (integrable_thetaDensity.integrableOn) measurableSet_Ioc
        (fun u hu => thetaDensity_ge_on_first_block hu)
    rw [hconst] at hmono
    calc (2 * Real.exp (-(2 * Real.pi))) * Real.log 2
        = (Real.log 2) * (2 * Real.exp (-(2 * Real.pi))) := by ring
      _ ≤ _ := hmono
  refine le_trans hblock ?_
  exact MeasureTheory.setIntegral_le_integral integrable_thetaDensity
    (Filter.Eventually.of_forall thetaDensity_nonneg)

/-! ## Completion and functional-equation symmetry -/

/-- The reflected half of the archimedean theta measure. -/
def thetaMeasureReflected : Measure ℝ := Measure.map (fun u : ℝ => -u) thetaMeasure

/-- The completed even theta measure. -/
def thetaMeasureCompleted : Measure ℝ := thetaMeasure + thetaMeasureReflected

theorem measurable_neg_real : Measurable (fun u : ℝ => -u) := measurable_neg

theorem thetaMeasureReflected_apply {S : Set ℝ} (hS : MeasurableSet S) :
    thetaMeasureReflected S = thetaMeasure ((fun u : ℝ => -u) ⁻¹' S) := by
  rw [thetaMeasureReflected, Measure.map_apply measurable_neg_real hS]

instance : IsFiniteMeasure thetaMeasureReflected := by
  refine ⟨?_⟩
  rw [thetaMeasureReflected_apply MeasurableSet.univ]
  exact measure_lt_top thetaMeasure _

theorem thetaMeasureReflected_univ : thetaMeasureReflected Set.univ = thetaMeasure Set.univ := by
  rw [thetaMeasureReflected_apply MeasurableSet.univ, Set.preimage_univ]

instance : IsFiniteMeasure thetaMeasureCompleted := by
  rw [thetaMeasureCompleted]
  infer_instance

/-- **Equation (6), mass half.**  Completion doubles the absolute defect. -/
theorem thetaMeasureCompleted_real_univ :
    thetaMeasureCompleted.real Set.univ = 2 * thetaMeasure.real Set.univ :=
  measureReal_add_of_mass_eq thetaMeasure thetaMeasureReflected thetaMeasureReflected_univ

/-- The completed sample set: prime-power logarithms and their reflections. -/
def primePowerLogsCompleted : Set ℝ := primePowerLogs ∪ (fun u : ℝ => -u) '' primePowerLogs

theorem primePowerLogsCompleted_countable : primePowerLogsCompleted.Countable :=
  primePowerLogs_countable.union (primePowerLogs_countable.image _)

theorem isClosed_primePowerLogsCompleted : IsClosed primePowerLogsCompleted := by
  refine isClosed_primePowerLogs.union ?_
  have himg : (fun u : ℝ => -u) '' primePowerLogs = (fun u : ℝ => -u) ⁻¹' primePowerLogs := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro hu
      exact ⟨-u, hu, neg_neg u⟩
  rw [himg]
  exact isClosed_primePowerLogs.preimage continuous_neg

theorem thetaMeasureCompleted_primePowerLogsCompleted :
    thetaMeasureCompleted primePowerLogsCompleted = 0 := by
  have hmeas : MeasurableSet primePowerLogsCompleted :=
    primePowerLogsCompleted_countable.measurableSet
  rw [thetaMeasureCompleted, Measure.add_apply,
    thetaMeasure_countable primePowerLogsCompleted_countable,
    thetaMeasureReflected_apply hmeas,
    thetaMeasure_countable (primePowerLogsCompleted_countable.preimage (fun a b h => by
      simpa using congrArg Neg.neg h))]
  norm_num

/-- **Equation (6).**  The completed source loses twice the mass to completed prime-power
sampling. -/
theorem isLUB_thetaCompletedSamplingPairings :
    IsLUB (samplingPairings thetaMeasureCompleted primePowerLogsCompleted)
      (2 * thetaMeasure.real Set.univ) := by
  rw [← thetaMeasureCompleted_real_univ]
  exact isLUB_samplingPairings thetaMeasureCompleted isClosed_primePowerLogsCompleted
    thetaMeasureCompleted_primePowerLogsCompleted

/-- **Equation (7).**  The normalized defect stays at its maximal value one after completion. -/
theorem normalized_thetaCompleted_defect :
    (thetaMeasureCompleted.real Set.univ) / (thetaMeasureCompleted.real Set.univ) = 1 := by
  refine normalized_samplingDefect thetaMeasureCompleted isClosed_primePowerLogsCompleted
    thetaMeasureCompleted_primePowerLogsCompleted ?_
  intro hzero
  have hmass : thetaMeasureCompleted.real Set.univ = 0 := by
    rw [MeasureTheory.measureReal_def, hzero, ENNReal.toReal_zero]
  rw [thetaMeasureCompleted_real_univ] at hmass
  have hpos : 0 < thetaMeasure.real Set.univ := by
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have := thetaMass_ge
    have hexp : (0 : ℝ) < 2 * Real.exp (-(2 * Real.pi)) := by positivity
    nlinarith
  linarith

/-- **The lost mass is the central completed theta trace.** -/
theorem thetaMass_eq_completedRiemannZeta₀ :
    ((thetaMeasure.real Set.univ : ℝ) : ℂ) = completedRiemannZeta₀ ((1 : ℂ) / 2) := by
  have h := completedRiemannZeta₀_critical_eq_re_positiveFourier 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, zero_div] at h
  rw [h]
  congr 1
  rw [thetaMeasure_real_univ]
  have hF : 𝓕 xiThetaPositiveSource 0 = ∫ u, xiThetaPositiveSource u := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp
  rw [hF]
  have hre : (∫ u, xiThetaPositiveSource u).re = ∫ u, (xiThetaPositiveSource u).re :=
    (Complex.reCLM.integral_comp_comm xiThetaPositiveSource_integrable).symm
  rw [hre]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun u => thetaDensity_eq_re u))

end RHTower.ArchimedeanSampling
