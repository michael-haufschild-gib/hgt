import GaloisForLFunctions.RHTower.StationaryRecurrencePointSpectrumLaw

/-!
# Exact point-spectrum scaling of stationary recurrence

The complete centered-time survival-fidelity law of an arbitrary probability
energy spectrum is the stationary law of its normalized point spectrum,
scaled by the square of the total point-spectrum mass.  Thus absolutely
continuous and singular-continuous sectors disappear from every stationary
return statistic, not only from mean return.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory Topology Polynomial

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Set of energies carrying positive singleton mass. -/
def pointSpectrumSet (mu : Measure ℝ) : Set ℝ :=
  {x : ℝ | mu {x} ≠ 0}

theorem pointSpectrumSet_countable
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    (pointSpectrumSet mu).Countable :=
  countable_atoms mu

theorem pointSpectrumSet_measurable
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    MeasurableSet (pointSpectrumSet mu) :=
  (pointSpectrumSet_countable mu).measurableSet

/-- Canonical finite measure obtained by restricting to the point spectrum. -/
def pointSpectrumFiniteMeasure
    (mu : Measure ℝ) [IsFiniteMeasure mu] : FiniteMeasure ℝ :=
  ⟨mu.restrict (pointSpectrumSet mu), inferInstance⟩

/-- Normalized point-spectrum probability law.  If the point spectrum has
zero mass, `FiniteMeasure.normalize` supplies an arbitrary point mass; the
fidelity scaling factor below is then zero. -/
def normalizedPointSpectrumLaw
    (mu : Measure ℝ) [IsFiniteMeasure mu] : ProbabilityMeasure ℝ :=
  (pointSpectrumFiniteMeasure mu).normalize

/-- Total mass carried by point spectrum. -/
def pointSpectrumMass
    (mu : Measure ℝ) [IsFiniteMeasure mu] : ENNReal :=
  (pointSpectrumFiniteMeasure mu : Measure ℝ) Set.univ

theorem pointSpectrumFiniteMeasure_eq_mass_smul_normalized
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    (pointSpectrumFiniteMeasure mu : Measure ℝ) =
      pointSpectrumMass mu •
        (normalizedPointSpectrumLaw mu : Measure ℝ) := by
  calc
    (pointSpectrumFiniteMeasure mu : Measure ℝ) =
        (pointSpectrumFiniteMeasure mu).mass •
          ((pointSpectrumFiniteMeasure mu).normalize : Measure ℝ) := by
      exact congrArg FiniteMeasure.toMeasure
        (pointSpectrumFiniteMeasure mu).self_eq_mass_smul_normalize
    _ = pointSpectrumMass mu •
          (normalizedPointSpectrumLaw mu : Measure ℝ) := by
      ext s hs
      simp [pointSpectrumMass, normalizedPointSpectrumLaw,
        ← FiniteMeasure.ennreal_mass]

/-- Restriction to point spectrum preserves every singleton mass. -/
theorem pointSpectrumFiniteMeasure_samePointMasses
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    SamePointMasses mu (pointSpectrumFiniteMeasure mu : Measure ℝ) := by
  intro x
  rw [pointSpectrumFiniteMeasure, FiniteMeasure.toMeasure_mk,
    Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : mu {x} = 0
  · symm
    calc
      mu ({x} ∩ pointSpectrumSet mu) = 0 :=
        measure_mono_null Set.inter_subset_left hx
      _ = mu {x} := hx.symm
  · simp [pointSpectrumSet, hx]

theorem isFiniteMeasure_convPow_finite
    (mu : Measure ℝ) [IsFiniteMeasure mu] (n : ℕ) :
    IsFiniteMeasure (convPow mu n) := by
  induction n with
  | zero =>
      rw [convPow]
      infer_instance
  | succ n ih =>
      rw [convPow]
      infer_instance

theorem isFiniteMeasure_spectralDifferenceMeasure_finite
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    IsFiniteMeasure (spectralDifferenceMeasure mu) := by
  rw [spectralDifferenceMeasure]
  infer_instance

/-- Convolution powers of finite measures preserve equality of all
singleton masses. -/
theorem convPow_samePointMasses_finite
    (mu nu : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : SamePointMasses mu nu)
    (n : ℕ) :
    SamePointMasses (convPow mu n) (convPow nu n) := by
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      rw [convPow, convPow]
      intro x
      letI : IsFiniteMeasure (convPow mu n) :=
        isFiniteMeasure_convPow_finite mu n
      letI : IsFiniteMeasure (convPow nu n) :=
        isFiniteMeasure_convPow_finite nu n
      exact conv_singleton_eq_of_samePointMasses
        mu nu (convPow mu n) (convPow nu n) h ih x

/-- Difference laws scale quadratically with spectral mass. -/
theorem spectralDifferenceMeasure_smul
    (nu : Measure ℝ) [SFinite nu]
    (c : ENNReal) :
    spectralDifferenceMeasure (c • nu) =
      (c ^ 2) • spectralDifferenceMeasure nu := by
  rw [spectralDifferenceMeasure, spectralDifferenceMeasure]
  rw [Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.map_smul, Measure.map_smul]
  rw [smul_smul, pow_two]

/-- Convolution powers scale by the corresponding power of total mass. -/
theorem convPow_smul
    (nu : Measure ℝ) [SFinite nu]
    (c : ENNReal) (n : ℕ) :
    convPow (c • nu) n =
      (c ^ n) • convPow nu n := by
  induction n with
  | zero => simp [convPow]
  | succ n ih =>
      rw [convPow, convPow, ih,
        Measure.conv_smul_left, Measure.conv_smul_right]
      rw [smul_smul, pow_succ']

theorem convPow_spectralDifference_pointSpectrum_singleton
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) (z : ℝ) :
    (convPow (spectralDifferenceMeasure mu) n) {z} =
      (convPow
        (spectralDifferenceMeasure
          (pointSpectrumFiniteMeasure mu : Measure ℝ)) n) {z} := by
  letI : IsFiniteMeasure
      (spectralDifferenceMeasure mu) :=
    isFiniteMeasure_spectralDifferenceMeasure_finite mu
  letI : IsFiniteMeasure
      (spectralDifferenceMeasure
        (pointSpectrumFiniteMeasure mu : Measure ℝ)) :=
    isFiniteMeasure_spectralDifferenceMeasure_finite
      (pointSpectrumFiniteMeasure mu : Measure ℝ)
  exact convPow_samePointMasses_finite
    (spectralDifferenceMeasure mu)
    (spectralDifferenceMeasure
      (pointSpectrumFiniteMeasure mu : Measure ℝ))
    (spectralDifferenceMeasure_samePointMasses
      mu (pointSpectrumFiniteMeasure mu : Measure ℝ)
      (pointSpectrumFiniteMeasure_samePointMasses mu))
    n z

/-- The full collision measure of the point spectrum is the normalized
point-spectrum collision measure scaled by `p^(2n)`. -/
theorem convPow_spectralDifference_pointSpectrum_eq_smul
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) :
    convPow
        (spectralDifferenceMeasure
          (pointSpectrumFiniteMeasure mu : Measure ℝ)) n =
      ((pointSpectrumMass mu) ^ (2 * n)) •
        convPow
          (spectralDifferenceMeasure
            (normalizedPointSpectrumLaw mu : Measure ℝ)) n := by
  rw [pointSpectrumFiniteMeasure_eq_mass_smul_normalized]
  rw [spectralDifferenceMeasure_smul, convPow_smul]
  congr 1
  rw [← pow_mul]

/-- Real point-spectrum mass used to scale fidelity. -/
def pointSpectrumMassReal
    (mu : Measure ℝ) [IsFiniteMeasure mu] : ℝ :=
  (pointSpectrumMass mu).toReal

theorem pointSpectrumMass_le_one
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    pointSpectrumMass mu ≤ 1 := by
  change
    (mu.restrict (pointSpectrumSet mu)) Set.univ ≤ 1
  rw [Measure.restrict_apply_univ]
  calc
    mu (pointSpectrumSet mu) ≤ mu Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem pointSpectrumMassReal_mem_unitInterval
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    pointSpectrumMassReal mu ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · simpa [pointSpectrumMassReal] using
      ENNReal.toReal_mono
        ENNReal.one_ne_top (pointSpectrumMass_le_one mu)

/-- Every stationary fidelity moment is the corresponding normalized
point-spectrum moment multiplied by `p^(2n)`. -/
theorem stationarySpectralReturnMoment_pointSpectrum_scale
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) :
    (∫ x, (x : ℝ) ^ n
        ∂(stationarySpectralReturnProbabilityMeasure mu :
          Measure SpectralReturnFidelityInterval)) =
      (pointSpectrumMassReal mu) ^ (2 * n) *
        (∫ x, (x : ℝ) ^ n
          ∂(stationarySpectralReturnProbabilityMeasure
              (normalizedPointSpectrumLaw mu : Measure ℝ) :
            Measure SpectralReturnFidelityInterval)) := by
  rw [stationarySpectralReturnProbabilityMeasure_moment,
    stationarySpectralReturnProbabilityMeasure_moment]
  simp only [Measure.real]
  rw [convPow_spectralDifference_pointSpectrum_singleton mu n 0]
  rw [convPow_spectralDifference_pointSpectrum_eq_smul mu n]
  simp [Measure.smul_apply, pointSpectrumMassReal]

/-- Fidelity contraction by squared point-spectrum mass. -/
def pointSpectrumFidelityScale
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    SpectralReturnFidelityInterval → SpectralReturnFidelityInterval :=
  fun x =>
    ⟨(pointSpectrumMassReal mu) ^ 2 * (x : ℝ), by
      have hp := pointSpectrumMassReal_mem_unitInterval mu
      constructor
      · exact mul_nonneg (sq_nonneg _) x.2.1
      · have hpSq : pointSpectrumMassReal mu ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]
        have hscale :
            pointSpectrumMassReal mu ^ 2 * (x : ℝ) ≤
              pointSpectrumMassReal mu ^ 2 := by
          nlinarith [mul_nonneg
            (sq_nonneg (pointSpectrumMassReal mu))
            (sub_nonneg.mpr x.2.2)]
        exact hscale.trans hpSq⟩

theorem pointSpectrumFidelityScale_continuous
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    Continuous (pointSpectrumFidelityScale mu) := by
  apply Continuous.subtype_mk
  fun_prop

/-- Stationary law of normalized point spectrum after fidelity scaling. -/
def scaledPointSpectrumStationaryReturnLaw
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  ProbabilityMeasure.map
    (stationarySpectralReturnProbabilityMeasure
      (normalizedPointSpectrumLaw mu : Measure ℝ))
    (f := pointSpectrumFidelityScale mu)
    (pointSpectrumFidelityScale_continuous mu).aemeasurable

/-- **Universal point-spectrum scaling law.** The complete stationary
survival-fidelity distribution of every probability energy law is exactly
the stationary law of its normalized point spectrum, contracted by the
square of total point-spectrum mass. -/
theorem stationarySpectralReturnProbabilityMeasure_eq_scaledPointSpectrum
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    stationarySpectralReturnProbabilityMeasure mu =
      scaledPointSpectrumStationaryReturnLaw mu := by
  apply spectralReturnFidelityInterval_probabilityMeasure_ext_moments
  intro n
  rw [stationarySpectralReturnMoment_pointSpectrum_scale]
  rw [scaledPointSpectrumStationaryReturnLaw,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (pointSpectrumFidelityScale_continuous mu).aemeasurable
    (by fun_prop)]
  change
    pointSpectrumMassReal mu ^ (2 * n) *
        (∫ x, (x : ℝ) ^ n
          ∂(stationarySpectralReturnProbabilityMeasure
              (normalizedPointSpectrumLaw mu : Measure ℝ) :
            Measure SpectralReturnFidelityInterval)) =
      ∫ x,
        (pointSpectrumMassReal mu ^ 2 * (x : ℝ)) ^ n
          ∂(stationarySpectralReturnProbabilityMeasure
              (normalizedPointSpectrumLaw mu : Measure ℝ) :
            Measure SpectralReturnFidelityInterval)
  rw [show
      (fun x : SpectralReturnFidelityInterval =>
        (pointSpectrumMassReal mu ^ 2 * (x : ℝ)) ^ n) =
      fun x : SpectralReturnFidelityInterval =>
        pointSpectrumMassReal mu ^ (2 * n) * (x : ℝ) ^ n by
      funext x
      rw [mul_pow, ← pow_mul]]
  rw [integral_const_mul]

end RHTower
