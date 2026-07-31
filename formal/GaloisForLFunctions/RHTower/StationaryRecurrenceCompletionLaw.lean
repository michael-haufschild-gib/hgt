import GaloisForLFunctions.RHTower.ObserverRecurrenceDistributionLaw
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw
import Mathlib.MeasureTheory.Measure.Prokhorov

open Complex Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory Topology Polynomial

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

lemma clockSampledSpectralReturnMoment_centeredUniform
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) {A : ℝ} (hA : 0 < A) :
    clockSampledSpectralReturnMoment
        (centeredUniformClockProbabilityMeasure A) mu n =
      spectralReturnMomentMean mu n A := by
  rw [clockSampledSpectralReturnMoment_eq_clockTransferCollision,
    spectralReturnMomentMean_eq_integral_sinc mu n hA]
  apply integral_congr_ae
  filter_upwards with x
  rw [charFun_centeredUniformClockProbabilityMeasure]

/-- Compact fidelity carrier. -/
abbrev SpectralReturnFidelityInterval := Set.Icc (0 : ℝ) 1

/-- Survival fidelity as a point of its exact compact range. -/
def spectralReturnFidelityPoint
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (t : ℝ) :
    SpectralReturnFidelityInterval :=
  ⟨Complex.normSq (charFun mu t), normSq_charFun_mem_Icc mu t⟩

theorem spectralReturnFidelityPoint_continuous
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    Continuous (spectralReturnFidelityPoint mu) :=
  (Complex.continuous_normSq.comp continuous_charFun).subtype_mk _

/-- Centered-window survival-fidelity law on the exact compact carrier. -/
def centeredSpectralReturnProbabilityMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (A : ℝ) :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  ProbabilityMeasure.map
    (centeredUniformClockProbabilityMeasure A)
    (f := spectralReturnFidelityPoint mu)
    (spectralReturnFidelityPoint_continuous mu).aemeasurable

/-- Continuous `n`-th moment reporter on the compact fidelity carrier. -/
def spectralReturnMomentContinuousMap (n : ℕ) :
    C(SpectralReturnFidelityInterval, ℝ) :=
  ⟨fun x => (x : ℝ) ^ n, by fun_prop⟩

theorem integral_pow_centeredSpectralReturnProbabilityMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) {A : ℝ} (hA : 0 < A) :
    (∫ x, (x : ℝ) ^ n
        ∂(centeredSpectralReturnProbabilityMeasure mu A :
          Measure SpectralReturnFidelityInterval)) =
      spectralReturnMomentMeanReal mu n A := by
  rw [centeredSpectralReturnProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (spectralReturnFidelityPoint_continuous mu).aemeasurable
    (by fun_prop)]
  have h :=
    clockSampledSpectralReturnMoment_centeredUniform
      mu n hA
  rw [spectralReturnMomentMean_eq_ofReal] at h
  rw [clockSampledSpectralReturnMoment] at h
  have hcast :
      (∫ t,
        ((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ)
        ∂(centeredUniformClockProbabilityMeasure A : Measure ℝ)) =
        ((∫ t,
          Complex.normSq (charFun mu t) ^ n
          ∂(centeredUniformClockProbabilityMeasure A : Measure ℝ) : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [hcast] at h
  change
    (∫ t,
      Complex.normSq (charFun mu t) ^ n
      ∂(centeredUniformClockProbabilityMeasure A : Measure ℝ)) =
        spectralReturnMomentMeanReal mu n A
  exact_mod_cast h

theorem tendsto_integral_pow_centeredSpectralReturnProbabilityMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    Tendsto
      (fun A =>
        ∫ x, (x : ℝ) ^ n
          ∂(centeredSpectralReturnProbabilityMeasure mu A :
            Measure SpectralReturnFidelityInterval))
      atTop
      (𝓝 ((convPow
        (spectralDifferenceMeasure mu) n).real {0})) := by
  apply
    (spectralReturnMomentMeanReal_tendsto_collisionHierarchy
      mu n).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  exact
    (integral_pow_centeredSpectralReturnProbabilityMeasure
      mu n hA).symm

theorem spectralReturnFidelityInterval_probabilityMeasure_ext_moments
    (mu nu : ProbabilityMeasure SpectralReturnFidelityInterval)
    (hmoments :
      ∀ n : ℕ,
        (∫ x, (x : ℝ) ^ n
            ∂(mu : Measure SpectralReturnFidelityInterval)) =
          ∫ x, (x : ℝ) ^ n
            ∂(nu : Measure SpectralReturnFidelityInterval)) :
    mu = nu := by
  let inclusion :
      SpectralReturnFidelityInterval → ℝ :=
    fun x => x
  have hinclusion : MeasurableEmbedding inclusion :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  let muReal : Measure ℝ :=
    Measure.map inclusion (mu : Measure SpectralReturnFidelityInterval)
  let nuReal : Measure ℝ :=
    Measure.map inclusion (nu : Measure SpectralReturnFidelityInterval)
  have hcarried : muReal (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    dsimp [muReal]
    rw [hinclusion.map_apply]
    have hpre :
        inclusion ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ = ∅ := by
      ext x
      simp [inclusion]
    rw [hpre, measure_empty]
  have hintegrable (lambda : ProbabilityMeasure SpectralReturnFidelityInterval)
      (n : ℕ) :
      Integrable (fun x : ℝ => x ^ n)
        (Measure.map inclusion
          (lambda : Measure SpectralReturnFidelityInterval)) := by
    rw [hinclusion.integrable_map_iff]
    apply (integrable_const (1 : ℝ)).mono'
    · fun_prop
    · filter_upwards with x
      change |(x : ℝ) ^ n| ≤ 1
      rw [abs_of_nonneg (pow_nonneg x.2.1 n)]
      exact pow_le_one₀ x.2.1 x.2.2
  have hmap : muReal = nuReal := by
    apply
      HTGeometry.measure_eq_of_moments_eq_of_one_carried
        (s := fun n =>
          ∫ x, (x : ℝ) ^ n
            ∂(mu : Measure SpectralReturnFidelityInterval))
        (c := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ))
        (by norm_num)
    · norm_num
      exact hcarried
    · intro k
      dsimp [muReal]
      rw [hinclusion.integral_map]
    · intro k
      exact hintegrable mu k
    · intro k
      dsimp [nuReal]
      rw [hinclusion.integral_map]
      exact hmoments k
    · intro k
      exact hintegrable nu k
  apply ProbabilityMeasure.toMeasure_injective
  exact hinclusion.map_injective hmap

theorem mapClusterPt_centeredSpectralReturn_moments
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (nu : ProbabilityMeasure SpectralReturnFidelityInterval)
    (hnu :
      MapClusterPt nu atTop
        (centeredSpectralReturnProbabilityMeasure mu)) :
    ∀ n : ℕ,
      (∫ x, (x : ℝ) ^ n
          ∂(nu : Measure SpectralReturnFidelityInterval)) =
        (convPow (spectralDifferenceMeasure mu) n).real {0} := by
  intro n
  obtain ⟨psi, hmeasure, hpsi⟩ := hnu.exists_seq_tendsto
  have hcontinuous :
      Continuous
        (fun lambda :
            ProbabilityMeasure SpectralReturnFidelityInterval =>
          ∫ x, (x : ℝ) ^ n
            ∂(lambda : Measure SpectralReturnFidelityInterval)) :=
    ProbabilityMeasure.continuous_integral_continuousMap
      (spectralReturnMomentContinuousMap n)
  have hleft :
      Tendsto
        (fun k =>
          ∫ x, (x : ℝ) ^ n
            ∂(centeredSpectralReturnProbabilityMeasure
              mu (psi k) :
                Measure SpectralReturnFidelityInterval))
        atTop
        (𝓝
          (∫ x, (x : ℝ) ^ n
            ∂(nu : Measure SpectralReturnFidelityInterval))) := by
    simpa [Function.comp_def, spectralReturnMomentContinuousMap] using
      hcontinuous.continuousAt.tendsto.comp hmeasure
  have hright :
      Tendsto
        (fun k =>
          ∫ x, (x : ℝ) ^ n
            ∂(centeredSpectralReturnProbabilityMeasure
              mu (psi k) :
                Measure SpectralReturnFidelityInterval))
        atTop
        (𝓝 ((convPow
          (spectralDifferenceMeasure mu) n).real {0})) := by
    simpa [Function.comp_def] using
      (tendsto_integral_pow_centeredSpectralReturnProbabilityMeasure
        mu n).comp hpsi
  exact tendsto_nhds_unique hleft hright

/-- Every real probability spectrum has one unique completed-time return
law, and its complete moment sequence is the additive gap-collision
hierarchy. -/
theorem existsUnique_stationarySpectralReturnProbabilityMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ∃! nu : ProbabilityMeasure SpectralReturnFidelityInterval,
      Tendsto
        (centeredSpectralReturnProbabilityMeasure mu)
        atTop (𝓝 nu) ∧
      ∀ n : ℕ,
        (∫ x, (x : ℝ) ^ n
            ∂(nu : Measure SpectralReturnFidelityInterval)) =
          (convPow (spectralDifferenceMeasure mu) n).real {0} := by
  have hfrequent :
      ∃ᶠ A in atTop,
        centeredSpectralReturnProbabilityMeasure mu A ∈
          (Set.univ :
            Set (ProbabilityMeasure SpectralReturnFidelityInterval)) :=
    Filter.Eventually.frequently
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
  obtain ⟨nu, hnuMem, hnuCluster⟩ :=
    (isCompact_univ :
      IsCompact
        (Set.univ :
          Set (ProbabilityMeasure SpectralReturnFidelityInterval))).exists_mapClusterPt_of_frequently
      hfrequent
  have hnuMoments :=
    mapClusterPt_centeredSpectralReturn_moments mu nu hnuCluster
  have htendsto :
      Tendsto
        (centeredSpectralReturnProbabilityMeasure mu)
        atTop (𝓝 nu) := by
    apply tendsto_nhds_of_unique_mapClusterPt
    intro lambda hlambda
    apply spectralReturnFidelityInterval_probabilityMeasure_ext_moments
    intro n
    rw [
      mapClusterPt_centeredSpectralReturn_moments
        mu lambda hlambda n,
      hnuMoments n]
  refine ⟨nu, ⟨htendsto, hnuMoments⟩, ?_⟩
  intro lambda hlambda
  exact tendsto_nhds_unique hlambda.1 htendsto

/-- Canonical completed-time survival-fidelity law of an arbitrary
probability energy spectrum. -/
def stationarySpectralReturnProbabilityMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  Classical.choose
    (existsUnique_stationarySpectralReturnProbabilityMeasure mu)

/-- Centered uniform time sampling converges weakly to the canonical
stationary return law. -/
theorem centeredSpectralReturnProbabilityMeasure_tendsto_stationary
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    Tendsto
      (centeredSpectralReturnProbabilityMeasure mu)
      atTop
      (𝓝 (stationarySpectralReturnProbabilityMeasure mu)) :=
  (Classical.choose_spec
    (existsUnique_stationarySpectralReturnProbabilityMeasure mu)).1.1

/-- Every moment of the stationary return law is exactly one additive
energy-gap collision probability. -/
theorem stationarySpectralReturnProbabilityMeasure_moment
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    (∫ x, (x : ℝ) ^ n
        ∂(stationarySpectralReturnProbabilityMeasure mu :
          Measure SpectralReturnFidelityInterval)) =
      (convPow (spectralDifferenceMeasure mu) n).real {0} :=
  (Classical.choose_spec
    (existsUnique_stationarySpectralReturnProbabilityMeasure mu)).1.2 n

/-- Zero fidelity as a point of the compact fidelity carrier. -/
def zeroSpectralReturnFidelity : SpectralReturnFidelityInterval :=
  ⟨0, by simp⟩

/-- Point mass at zero fidelity. -/
def zeroSpectralReturnProbabilityMeasure :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  ⟨Measure.dirac zeroSpectralReturnFidelity,
    Measure.dirac.isProbabilityMeasure⟩

/-- **Atomless stationary collapse.** Every atomless probability energy
spectrum—absolutely continuous or singular continuous—has the same
completed-time survival-fidelity law: the point mass at zero. -/
theorem stationarySpectralReturnProbabilityMeasure_eq_zero_of_noAtoms
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    [NullSingletonClass mu] :
    stationarySpectralReturnProbabilityMeasure mu =
      zeroSpectralReturnProbabilityMeasure := by
  apply spectralReturnFidelityInterval_probabilityMeasure_ext_moments
  intro n
  rw [stationarySpectralReturnProbabilityMeasure_moment]
  by_cases hn : n = 0
  · subst n
    simp [zeroSpectralReturnProbabilityMeasure, convPow,
      Measure.real]
  · rw [spectralCollisionHierarchy_eq_zero_of_noAtoms
      mu (Nat.pos_of_ne_zero hn)]
    simp [zeroSpectralReturnProbabilityMeasure,
      zeroSpectralReturnFidelity, hn]

end RHTower
