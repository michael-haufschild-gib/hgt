import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus
import GaloisForLFunctions.HTGeometry.PhaseFunctionBohrCoefficient
import GaloisForLFunctions.HTGeometry.GaussianRadialContinuousReporter

/-!
# The completed-time Haar average is the Bohr mean

Uniformly sampled clock time on the window `(0, T]` pushes forward to a
probability law on the phase torus whose integrals are exactly window averages.
Every torus character pulls back to a Bohr character, so these integrals converge
to the zero-detuning indicator, which is also the Haar integral of the character
over the completed time.  Weak convergence therefore identifies the Haar integral
of every continuous function over the completed time with the Bohr mean of its
pullback along the clock.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d]

/-- A positive window length, equal to the given one when that is positive. -/
def windowLength (T : ℝ) : ℝ := if 0 < T then T else 1

theorem windowLength_pos (T : ℝ) : 0 < windowLength T := by
  unfold windowLength
  split
  · assumption
  · norm_num

theorem windowLength_eq {T : ℝ} (hT : 0 < T) : windowLength T = T := if_pos hT

/-- Uniformly sampled observation time on the window `(0, T]`. -/
def windowProbabilityMeasure (T : ℝ) : ProbabilityMeasure ℝ :=
  ⟨(ENNReal.ofReal (windowLength T))⁻¹ •
      volume.restrict (Set.Ioc 0 (windowLength T)), by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by
      simpa using (ENNReal.ofReal_pos.mpr (windowLength_pos T)).ne')
      ENNReal.ofReal_ne_top⟩

/-- The clock-phase law of uniformly sampled observation time. -/
def clockPhaseWindowLaw (omega : d → ℝ) (T : ℝ) :
    ProbabilityMeasure (UnitAddTorus d) :=
  ProbabilityMeasure.map (windowProbabilityMeasure T)
    (finiteClockPhasePoint_continuous omega).aemeasurable

/-- The clock-phase law integrates continuous functions to window averages. -/
theorem integral_clockPhaseWindowLaw (omega : d → ℝ) {T : ℝ} (hT : 0 < T)
    (f : C(UnitAddTorus d, ℂ)) :
    (∫ x, f x ∂(clockPhaseWindowLaw omega T : Measure (UnitAddTorus d)))
      = windowAverage (fun s : ℝ => f (finiteClockPhasePoint omega s)) T := by
  rw [clockPhaseWindowLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (finiteClockPhasePoint_continuous omega).aemeasurable
      f.continuous.aestronglyMeasurable]
  show (∫ s, f (finiteClockPhasePoint omega s)
      ∂((ENNReal.ofReal (windowLength T))⁻¹ •
        volume.restrict (Set.Ioc 0 (windowLength T)))) = _
  rw [integral_smul_measure, windowLength_eq hT, windowAverage,
    ← intervalIntegral.integral_of_le (le_of_lt hT)]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hT)]

/-- Every torus character has window averages converging to its zero-detuning
indicator. -/
theorem tendsto_integral_mFourier_clockPhaseWindowLaw (omega : d → ℝ) (n : d → ℤ) :
    Tendsto
      (fun T : ℝ => ∫ x, UnitAddTorus.mFourier n x
        ∂(clockPhaseWindowLaw omega T : Measure (UnitAddTorus d)))
      atTop
      (𝓝 (if finiteTorusCharacterDetuning n omega = 0 then (1 : ℂ) else 0)) := by
  have hchar : ∀ s : ℝ,
      UnitAddTorus.mFourier n (finiteClockPhasePoint omega s)
        = expChar (finiteTorusCharacterDetuning n omega) s :=
    fun s => mFourier_finiteClockPhasePoint_expChar n omega s
  have hmean : bohrMean (expChar (finiteTorusCharacterDetuning n omega))
      = if finiteTorusCharacterDetuning n omega = 0 then (1 : ℂ) else 0 :=
    bohrMean_expChar _
  have hlim := tendsto_windowAverage_bohrMean
    (continuous_expChar (finiteTorusCharacterDetuning n omega))
    (isBohrAlmostPeriodic_expChar (finiteTorusCharacterDetuning n omega))
  rw [hmean] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [integral_clockPhaseWindowLaw omega hT]
  congr 1
  funext s
  exact (hchar s).symm

/-- **Completed-time equidistribution for the one-sided window.**  Uniformly
sampled clock time on `(0, T]` converges weakly to Haar measure of the completed
time. -/
theorem tendsto_clockPhaseWindowLaw_orbitClosureHaar {k : Type} [Fintype k]
    (omega : d → ℝ) (gamma : k → ℝ) (M : d → k → ℤ)
    (hgamma : RationallyIndependentFrequency gamma)
    (hM : ∀ i, omega i = ∑ j, (M i j : ℝ) * gamma j) :
    Tendsto (clockPhaseWindowLaw omega) atTop (𝓝 (orbitClosureHaar M)) := by
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro n
  rw [orbitClosureHaar_mFourier_integral]
  have hdet := finiteTorusCharacterDetuning_of_integer_presentation omega gamma M hM n
  have hiff : finiteTorusCharacterDetuning n omega = 0
      ↔ (fun j => ∑ i, n i * M i j) = 0 := by
    rw [hdet]
    constructor
    · intro h
      exact hgamma _ h
    · intro h
      rw [h]
      unfold finiteTorusCharacterDetuning
      simp
  have hlim := tendsto_integral_mFourier_clockPhaseWindowLaw omega n
  by_cases hn : (fun j => ∑ i, n i * M i j) = 0
  · rw [if_pos hn]
    rw [if_pos (hiff.mpr hn)] at hlim
    exact hlim
  · rw [if_neg hn]
    rw [if_neg (fun h => hn (hiff.mp h))] at hlim
    exact hlim

section ComplexWeakConvergence

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X]

/-- A continuous function on a compact space is integrable against a probability
measure. -/
theorem integrable_continuous_of_compactSpace (ν : Measure X) [IsProbabilityMeasure ν]
    (g : C(X, ℂ)) : Integrable (fun x => g x) ν :=
  g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Splitting a complex integral into its real and imaginary parts. -/
theorem integral_complex_split (ν : Measure X) [IsProbabilityMeasure ν] (g : C(X, ℂ)) :
    (∫ x, g x ∂ν)
      = ((∫ x, (g x).re ∂ν : ℝ) : ℂ) + ((∫ x, (g x).im ∂ν : ℝ) : ℂ) * Complex.I := by
  have hint : Integrable (fun x => g x) ν := integrable_continuous_of_compactSpace ν g
  have hre : (∫ x, (g x).re ∂ν) = (∫ x, g x ∂ν).re :=
    (Complex.reCLM.integral_comp_comm hint)
  have him : (∫ x, (g x).im ∂ν) = (∫ x, g x ∂ν).im :=
    (Complex.imCLM.integral_comp_comm hint)
  rw [hre, him]
  exact (Complex.re_add_im _).symm

/-- Weak convergence of probability measures on a compact space transfers to
complex-valued continuous integrands. -/
theorem tendsto_integral_of_tendsto_probabilityMeasure
    {μs : ℝ → ProbabilityMeasure X} {mu : ProbabilityMeasure X}
    (h : Tendsto μs atTop (𝓝 mu)) (g : C(X, ℂ)) :
    Tendsto (fun T : ℝ => ∫ x, g x ∂(μs T : Measure X)) atTop
      (𝓝 (∫ x, g x ∂(mu : Measure X))) := by
  have hforall := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h
  have hre := hforall (BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (g x).re, Complex.continuous_re.comp g.continuous⟩)
  have him := hforall (BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (g x).im, Complex.continuous_im.comp g.continuous⟩)
  have hcombine : Tendsto
      (fun T : ℝ => ((∫ x, (g x).re ∂(μs T : Measure X) : ℝ) : ℂ)
        + ((∫ x, (g x).im ∂(μs T : Measure X) : ℝ) : ℂ) * Complex.I) atTop
      (𝓝 (((∫ x, (g x).re ∂(mu : Measure X) : ℝ) : ℂ)
        + ((∫ x, (g x).im ∂(mu : Measure X) : ℝ) : ℂ) * Complex.I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp hre).add
      (((Complex.continuous_ofReal.tendsto _).comp him).mul tendsto_const_nhds)
  rw [integral_complex_split (mu : Measure X) g]
  refine hcombine.congr fun T => ?_
  rw [← integral_complex_split (μs T : Measure X) g]

end ComplexWeakConvergence

section StateMap

variable {ι : Type} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The state map on the phase torus: the observer state assembled from the
spectral amplitudes at a phase point. -/
def torusStateMap (w : ι → E) (z : UnitAddTorus ι) : E :=
  ∑ i, (fourier 1 (z i) : ℂ) • w i

theorem continuous_torusStateMap (w : ι → E) : Continuous (torusStateMap w) := by
  unfold torusStateMap
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((fourier (1 : ℤ)).continuous.comp (continuous_apply i)).smul continuous_const

/-- The state curve is the state map along the clock phase. -/
theorem torusStateMap_finiteClockPhasePoint (Ev : ι → ℝ) (w : ι → E) (s : ℝ) :
    torusStateMap w (finiteClockPhasePoint (fun i => -Ev i) s)
      = spectralStateCurve Ev w s := by
  unfold torusStateMap spectralStateCurve finiteClockPhasePoint
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hcancel : (Real.pi : ℂ) * (Real.pi : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hpi
  field_simp
  push_cast
  linear_combination (-((s : ℂ) * ((Ev i : ℝ) : ℂ))) * hcancel

end StateMap

section HaarBohr

variable {ι : Type} [Fintype ι] {k : Type} [Fintype k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The completed-time Haar average is the Bohr mean.**  For every continuous
reporter, the Haar integral over the completed time of the reporter evaluated on
the state map equals the Bohr mean of the reporter along the state curve. -/
theorem integral_orbitClosureHaar_eq_bohrMean (Ev : ι → ℝ) (w : ι → E)
    (gamma : k → ℝ) (M : ι → k → ℤ)
    (hgamma : RationallyIndependentFrequency gamma)
    (hM : ∀ i, -Ev i = ∑ j, (M i j : ℝ) * gamma j)
    {F : E → ℂ} (hF : Continuous F) :
    (∫ z, F (torusStateMap w z) ∂(orbitClosureHaar M : Measure (UnitAddTorus ι)))
      = bohrMean fun s : ℝ => F (spectralStateCurve Ev w s) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  set g : C(UnitAddTorus ι, ℂ) :=
    ⟨fun z => F (torusStateMap w z), hF.comp (continuous_torusStateMap w)⟩ with hg
  have hweak := tendsto_clockPhaseWindowLaw_orbitClosureHaar
    (fun i => -Ev i) gamma M hgamma hM
  have hharr := tendsto_integral_of_tendsto_probabilityMeasure hweak g
  have hcurve : ∀ s : ℝ, g (finiteClockPhasePoint (fun i => -Ev i) s)
      = F (spectralStateCurve Ev w s) := by
    intro s
    rw [hg]
    exact congrArg F (torusStateMap_finiteClockPhasePoint Ev w s)
  have hbohr : Tendsto
      (fun T : ℝ => ∫ z, g z ∂(clockPhaseWindowLaw (fun i => -Ev i) T :
        Measure (UnitAddTorus ι))) atTop
      (𝓝 (bohrMean fun s : ℝ => F (spectralStateCurve Ev w s))) := by
    have hK : IsCompact (Metric.closedBall (0 : E) (∑ i, ‖w i‖)) :=
      isCompact_closedBall _ _
    have hrange : ∀ t : ℝ, spectralStateCurve Ev w t
        ∈ Metric.closedBall (0 : E) (∑ i, ‖w i‖) := by
      intro t
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_spectralStateCurve_le Ev w t
    have hap : HTGeometry.IsBohrAlmostPeriodic
        fun s : ℝ => F (spectralStateCurve Ev w s) :=
      isBohrAlmostPeriodic_comp_of_range_subset
        (isBohrAlmostPeriodic_spectralStateCurve Ev w) hK hrange hF.continuousOn
    have hlim := tendsto_windowAverage_bohrMean
      (hF.comp (continuous_spectralStateCurve Ev w)) hap
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [integral_clockPhaseWindowLaw (fun i => -Ev i) hT g]
    congr 1
    funext s
    exact (hcurve s).symm
  exact tendsto_nhds_unique hharr hbohr

end HaarBohr

end

end GaloisForLFunctions.HTGeometry
