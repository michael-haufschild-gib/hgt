import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinAbelTomography
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Gibbs free-energy corollary of confocal Abel tomography

The negative logarithm of the selected Abel radius is exactly twice the logarithmic confocal
amplitude.  Its zero set is the positive-source radical, while its first recession is the same
intrinsic transverse defect selected by the amplitude and radius laws.
-/

open Filter Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Logarithmic free energy of the confocal Abel radius. -/
def confocalGibbsFreeEnergy (S : Set ℂ) (R : ℝ) : ℝ :=
  -Real.log (HTGeometry.confocalAbelRadius S R)

/-- Exact free-energy/amplitude split. -/
theorem confocalGibbsFreeEnergy_eq_two_log_amplitude
    (S : Set ℂ) (R : ℝ) :
    confocalGibbsFreeEnergy S R =
      2 * Real.log (HTGeometry.confocalAmplitudeEnvelope S R) := by
  rw [confocalGibbsFreeEnergy, HTGeometry.confocalAbelRadius,
    Real.log_inv, Real.log_pow]
  norm_num

/-- The free-energy radical is exactly the vanishing transverse-defect locus. -/
theorem confocalGibbsFreeEnergy_eq_zero_iff_transverseDefectEnvelope_eq_zero
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hRM : M < R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    confocalGibbsFreeEnergy S R = 0 ↔
      HTGeometry.transverseDefectEnvelope S = 0 := by
  have hR : 0 < R := hM.trans_lt hRM
  have hBpos : 0 < HTGeometry.confocalAmplitudeEnvelope S R := by
    rw [HTGeometry.confocalAmplitudeEnvelope]
    have hDnonneg := HTGeometry.confocalDefectEnvelope_nonneg hne hR.le hbound
    have hquot : 0 ≤ HTGeometry.confocalDefectEnvelope S R / R :=
      div_nonneg hDnonneg hR.le
    linarith
  rw [confocalGibbsFreeEnergy_eq_two_log_amplitude]
  constructor
  · intro hzero
    have hlog : Real.log (HTGeometry.confocalAmplitudeEnvelope S R) = 0 := by
      linarith
    have hB : HTGeometry.confocalAmplitudeEnvelope S R = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hBpos hlog
    exact (HTGeometry.confocalAmplitudeEnvelope_eq_one_iff
      hne hM hRM hbound).mp hB
  · intro hzero
    have hB : HTGeometry.confocalAmplitudeEnvelope S R = 1 :=
      (HTGeometry.confocalAmplitudeEnvelope_eq_one_iff
        hne hM hRM hbound).mpr hzero
    rw [hB, Real.log_one]
    norm_num

/-- Equivalently, the free-energy radical consists exactly of sources supported on the
nonnegative real axis. -/
theorem confocalGibbsFreeEnergy_eq_zero_iff_source_positive
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hRM : M < R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    confocalGibbsFreeEnergy S R = 0 ↔ ∀ z ∈ S, (0 : ℂ) ≤ z := by
  rw [confocalGibbsFreeEnergy_eq_zero_iff_transverseDefectEnvelope_eq_zero
      hne hM hRM hbound,
    HTGeometry.transverseDefectEnvelope_eq_zero_iff hne hbound]

/-- The free-energy recession agrees with both the squared-amplitude and Abel-radius recessions. -/
theorem tendsto_mul_confocalGibbsFreeEnergy
    {S : Set ℂ} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    Tendsto (fun R : ℝ => R * confocalGibbsFreeEnergy S R) atTop
      (nhds (2 * HTGeometry.transverseDefectEnvelope S)) := by
  have hD := HTGeometry.tendsto_confocalDefectEnvelope_atTop hne hM hbound
  have hscaled : Tendsto
      (fun R : ℝ => R * (HTGeometry.confocalDefectEnvelope S R / R))
      atTop (nhds (HTGeometry.transverseDefectEnvelope S)) := by
    apply hD.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    field_simp [hR.ne']
  have hlog := Real.tendsto_mul_log_one_add_of_tendsto hscaled
  have htwice := hlog.const_mul 2
  apply htwice.congr'
  filter_upwards with R
  rw [confocalGibbsFreeEnergy_eq_two_log_amplitude,
    HTGeometry.confocalAmplitudeEnvelope]
  ring

end

end RHTower
