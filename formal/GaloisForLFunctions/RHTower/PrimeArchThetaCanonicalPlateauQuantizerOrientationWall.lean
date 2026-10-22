import GaloisForLFunctions.RHTower.PrimeArchObservableCarrierQuantization
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmQuantileNormalForm
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional
import Mathlib.Probability.Kernel.Representation

/-!
# Canonical theta plateau quantizer and the orientation wall

The canonical Xi thermal measure has atom mass equal to atom location.  Its total mass is the
zeroth completed prime--archimedean source moment without assuming RH.  Normalize this atomic
measure, realize it as a measurable image of the unit interval, and pull that realization back
through the probability-integral transform of the literal theta-cusp source.

This constructs the positive-fibre plateau quotient demanded by Route Q unconditionally.  It also
identifies the exact obstruction: the reporter's first-moment excess over the completed source is
the thermal orientation energy.  Thus plateau existence is kinematic; source orientation remains
equivalent to RH.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource

/-- The unconditional power moments of the canonical compact Xi measure are the positive thermal
moment tower.  No RH hypothesis is needed for this identity. -/
theorem integral_primeArchXiCompactMomentMeasure_eq_xiThermalPositiveMoment
    (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂primeArchXiCompactMomentMeasure =
      xiThermalPositiveMoment n := by
  rw [primeArchXiCompactMomentMeasure,
    integral_sum_dirac (fun j => by simp [ENNReal.ofReal_ne_top])]
  calc
    (∑' j : ℕ,
        (ENNReal.ofReal (xiThermalNode (xiThermalEnumeration j))).toReal •
          xiThermalNode (xiThermalEnumeration j) ^ n) =
        ∑' j : ℕ, xiThermalNode (xiThermalEnumeration j) ^ (n + 1) := by
      apply tsum_congr
      intro j
      rw [ENNReal.toReal_ofReal (xiThermalNode_pos _).le]
      simp only [smul_eq_mul]
      ring
    _ = xiThermalPositiveMoment n :=
      (hasSum_xiThermalEnumeration_positiveMoment n).tsum_eq

/-- The canonical Xi measure and the native completed source have the same total mass
unconditionally. -/
theorem primeArchXiCompactMomentMeasure_univ :
    primeArchXiCompactMomentMeasure Set.univ =
      ENNReal.ofReal (normalizedPrimeArchMoment 0) := by
  letI : IsFiniteMeasure primeArchXiCompactMomentMeasure :=
    primeArchXiCompactMomentMeasure_finite
  have h :=
    integral_primeArchXiCompactMomentMeasure_eq_xiThermalPositiveMoment 0
  simp only [pow_zero] at h
  rw [integral_const, xiThermalPositiveMoment_zero_eq_source] at h
  simp only [smul_eq_mul, mul_one] at h
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  simpa only [measureReal_def,
    ENNReal.toReal_ofReal normalizedPrimeArchMoment_zero_pos.le] using h

/-- Probability normalization of the canonical compact Xi measure. -/
def primeArchXiProbabilityMeasure : Measure ℝ :=
  (ENNReal.ofReal (normalizedPrimeArchMoment 0))⁻¹ •
    primeArchXiCompactMomentMeasure

instance primeArchXiProbabilityMeasure_isProbability :
    IsProbabilityMeasure primeArchXiProbabilityMeasure := by
  constructor
  rw [primeArchXiProbabilityMeasure, Measure.smul_apply,
    primeArchXiCompactMomentMeasure_univ]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr normalizedPrimeArchMoment_zero_pos).ne'
    ENNReal.ofReal_ne_top

/-- The literal theta-cusp probability-integral coordinate, bundled into the closed unit
interval.  Its values in fact lie in the open interval. -/
def routeQThetaCdfUnit (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨thetaSource.cdfFun x,
    (thetaSource.cdfFun_mem_Ioo x).1.le,
    (thetaSource.cdfFun_mem_Ioo x).2.le⟩

theorem measurable_routeQThetaCdfUnit : Measurable routeQThetaCdfUnit := by
  exact thetaSource.continuous_cdfFun.measurable.subtype_mk

/-- The bundled theta CDF sends the literal theta probability law to Lebesgue probability on the
closed unit interval. -/
theorem map_routeQThetaCdfUnit_law_eq_volume :
    Measure.map routeQThetaCdfUnit thetaSource.law =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_map measurable_subtype_coe measurable_routeQThetaCdfUnit,
    MeasurableSet.map_coe_volume measurableSet_Icc]
  change Measure.map thetaSource.cdfFun thetaSource.law =
    (volume : Measure ℝ).restrict (Set.Icc 0 1)
  rw [(HedenmalmQuantile.measurePreserving_cdf_unitInterval thetaSource).map_eq]
  rfl

/-- Native-mass theta source used by the Route-Q plateau reporter. -/
def routeQThetaPlateauSourceMeasure : Measure ℝ :=
  ENNReal.ofReal (normalizedPrimeArchMoment 0) • thetaSource.law

/-- **Unconditional theta-to-Xi plateau transport.**  A measurable reporter from the literal
theta-cusp law has exactly the canonical compact Xi measure as its native-mass pushforward. -/
theorem exists_routeQThetaPlateauReporter :
    ∃ Q : ℝ → ℝ, Measurable Q ∧
      Measure.map Q routeQThetaPlateauSourceMeasure =
        primeArchXiCompactMomentMeasure := by
  obtain ⟨f, hf, hfmap⟩ :=
    primeArchXiProbabilityMeasure.exists_measurable_map_eq
  let Q : ℝ → ℝ := f ∘ routeQThetaCdfUnit
  refine ⟨Q, hf.comp measurable_routeQThetaCdfUnit, ?_⟩
  let c : ℝ≥0∞ := ENNReal.ofReal (normalizedPrimeArchMoment 0)
  have hc0 : c ≠ 0 :=
    (ENNReal.ofReal_pos.mpr normalizedPrimeArchMoment_zero_pos).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    Measure.map Q routeQThetaPlateauSourceMeasure =
        c • Measure.map Q thetaSource.law := by
      rw [routeQThetaPlateauSourceMeasure]
      exact Measure.map_smul c thetaSource.law Q
    _ = c • Measure.map f
        (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
      congr 1
      change Measure.map (f ∘ routeQThetaCdfUnit) thetaSource.law = _
      rw [← Measure.map_map hf measurable_routeQThetaCdfUnit,
        map_routeQThetaCdfUnit_law_eq_volume]
    _ = c • primeArchXiProbabilityMeasure := by rw [hfmap]
    _ = primeArchXiCompactMomentMeasure := by
      rw [primeArchXiProbabilityMeasure, smul_smul,
        ENNReal.mul_inv_cancel hc0 hctop, one_smul]

/-- Every power of any canonical plateau reporter is exactly the corresponding unconditional
positive thermal moment. -/
theorem integral_routeQThetaPlateauReporter_pow
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hmap : Measure.map Q routeQThetaPlateauSourceMeasure =
      primeArchXiCompactMomentMeasure) (n : ℕ) :
    ∫ x : ℝ, Q x ^ n ∂routeQThetaPlateauSourceMeasure =
      xiThermalPositiveMoment n := by
  calc
    ∫ x : ℝ, Q x ^ n ∂routeQThetaPlateauSourceMeasure =
        ∫ y : ℝ, y ^ n ∂Measure.map Q routeQThetaPlateauSourceMeasure := by
      rw [integral_map hQ.aemeasurable
        (continuous_pow n |>.aestronglyMeasurable)]
    _ = ∫ y : ℝ, y ^ n ∂primeArchXiCompactMomentMeasure := by rw [hmap]
    _ = xiThermalPositiveMoment n :=
      integral_primeArchXiCompactMomentMeasure_eq_xiThermalPositiveMoment n

theorem integrable_routeQThetaPlateauReporter_pow
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hmap : Measure.map Q routeQThetaPlateauSourceMeasure =
      primeArchXiCompactMomentMeasure) (n : ℕ) :
    Integrable (fun x : ℝ => Q x ^ n) routeQThetaPlateauSourceMeasure := by
  have htarget : Integrable (fun y : ℝ => y ^ n)
      (Measure.map Q routeQThetaPlateauSourceMeasure) := by
    rw [hmap]
    exact integrable_primeArchXiCompactMomentMeasure n
  have hcomp := (integrable_map_measure
    (continuous_pow n |>.aestronglyMeasurable) hQ.aemeasurable).mp htarget
  change Integrable ((fun y : ℝ => y ^ n) ∘ Q)
    routeQThetaPlateauSourceMeasure
  exact hcomp

/-- The first nonconstant moment mismatch of every canonical theta plateau reporter is exactly
the thermal orientation energy. -/
theorem routeQThetaPlateauReporter_firstMomentDefect_eq_orientationEnergy
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hmap : Measure.map Q routeQThetaPlateauSourceMeasure =
      primeArchXiCompactMomentMeasure) :
    (∫ x : ℝ, Q x ∂routeQThetaPlateauSourceMeasure) -
        normalizedPrimeArchMoment 1 = xiThermalOrientationEnergy := by
  have hmoment := integral_routeQThetaPlateauReporter_pow hQ hmap 1
  simp only [pow_one, xiThermalPositiveMoment_one_eq_secondMoment] at hmoment
  linarith [xiThermalSecondMoment_sub_orientationEnergy_eq_source]

theorem routeQThetaPlateauReporter_firstMomentDefect_nonneg
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hmap : Measure.map Q routeQThetaPlateauSourceMeasure =
      primeArchXiCompactMomentMeasure) :
    0 ≤ (∫ x : ℝ, Q x ∂routeQThetaPlateauSourceMeasure) -
      normalizedPrimeArchMoment 1 := by
  rw [routeQThetaPlateauReporter_firstMomentDefect_eq_orientationEnergy hQ hmap]
  exact xiThermalOrientationEnergy_nonneg

/-- Exact orientation wall: the plateau reporter's barycenter matches the completed source iff
RH. -/
theorem routeQThetaPlateauReporter_firstMomentDefect_eq_zero_iff_rh
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hmap : Measure.map Q routeQThetaPlateauSourceMeasure =
      primeArchXiCompactMomentMeasure) :
    (∫ x : ℝ, Q x ∂routeQThetaPlateauSourceMeasure) -
        normalizedPrimeArchMoment 1 = 0 ↔ RiemannHypothesis := by
  rw [routeQThetaPlateauReporter_firstMomentDefect_eq_orientationEnergy hQ hmap,
    xiThermalOrientationEnergy_eq_zero_iff_rh]

/-- Every enumerated canonical thermal node has a positive theta-source fibre. -/
theorem routeQThetaPlateauReporter_levelSet_pos
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hmap : Measure.map Q routeQThetaPlateauSourceMeasure =
      primeArchXiCompactMomentMeasure) (j : ℕ) :
    0 < routeQThetaPlateauSourceMeasure
      (Q ⁻¹' {xiThermalNode (xiThermalEnumeration j)}) := by
  have heval := congrArg
    (fun μ : Measure ℝ => μ {xiThermalNode (xiThermalEnumeration j)}) hmap
  rw [Measure.map_apply hQ (measurableSet_singleton _)] at heval
  rw [heval]
  exact primeArchXiCompactMomentMeasure_singleton_pos j

/-- Complete moment-witness status of a canonical plateau reporter is still exactly RH. -/
theorem routeQThetaPlateauReporter_isWitness_iff_rh
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hmap : Measure.map Q routeQThetaPlateauSourceMeasure =
      primeArchXiCompactMomentMeasure) :
    IsPrimeArchObservableWitness routeQThetaPlateauSourceMeasure Q ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_primeArchMomentRepresentation
      h.pushforward_isMomentWitness.toRepresentation
  · intro hRH
    refine ⟨hQ, ?_, ?_⟩
    · intro n
      rw [integral_routeQThetaPlateauReporter_pow hQ hmap n]
      exact (xiThermalPositiveMoment_eq_source_iff_rh.mpr hRH).symm ▸ rfl
    · exact integrable_routeQThetaPlateauReporter_pow hQ hmap

/-- **Route-Q plateau orientation wall.**  One reporter simultaneously has the canonical Xi
pushforward, positive fibres over every thermal atom, all unconditional thermal moments, and an
exact nonnegative barycenter defect whose vanishing and complete witness status are equivalent to
RH.  Existence of a plateau quotient therefore supplies no missing orientation. -/
theorem exists_routeQThetaPlateauReporter_orientationWall :
    ∃ Q : ℝ → ℝ,
      Measurable Q ∧
      Measure.map Q routeQThetaPlateauSourceMeasure =
        primeArchXiCompactMomentMeasure ∧
      (∀ j : ℕ, 0 < routeQThetaPlateauSourceMeasure
        (Q ⁻¹' {xiThermalNode (xiThermalEnumeration j)})) ∧
      (∀ n : ℕ, ∫ x : ℝ, Q x ^ n ∂routeQThetaPlateauSourceMeasure =
        xiThermalPositiveMoment n) ∧
      0 ≤ (∫ x : ℝ, Q x ∂routeQThetaPlateauSourceMeasure) -
        normalizedPrimeArchMoment 1 ∧
      (((∫ x : ℝ, Q x ∂routeQThetaPlateauSourceMeasure) -
          normalizedPrimeArchMoment 1 = 0) ↔ RiemannHypothesis) ∧
      (IsPrimeArchObservableWitness routeQThetaPlateauSourceMeasure Q ↔
        RiemannHypothesis) := by
  obtain ⟨Q, hQ, hmap⟩ := exists_routeQThetaPlateauReporter
  refine ⟨Q, hQ, hmap, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => routeQThetaPlateauReporter_levelSet_pos hQ hmap j
  · exact fun n => integral_routeQThetaPlateauReporter_pow hQ hmap n
  · exact routeQThetaPlateauReporter_firstMomentDefect_nonneg hQ hmap
  · exact routeQThetaPlateauReporter_firstMomentDefect_eq_zero_iff_rh hQ hmap
  · exact routeQThetaPlateauReporter_isWitness_iff_rh hQ hmap

end

end RHTower
