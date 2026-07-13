import GaloisForLFunctions.HTGeometry.SchwartzPositiveMeasureRepresentation
import GaloisForLFunctions.RHTower.XiThetaSpectralOrientationClassification

/-!
# Universal positive-form classification at the Hedenmalm source

Every jointly continuous nonnegative momentum-symmetric Schwartz form has a canonical positive
temperate spectral measure.  This module specializes that representation to the Hedenmalm theta
source.  Theta nullity forces the measure onto the real `Xi` divisor, hence makes it purely atomic;
any nonzero such form is necessarily nonclosable through ordinary Lebesgue `L²`.

This is a carrier theorem, not an orientation theorem: it classifies every form after positivity
has been proved, but it does not prove positivity for the source-reconstructed Xi Bezoutian.
-/

open Complex Function Filter Set MeasureTheory
open scoped Topology FourierTransform SchwartzMap

noncomputable section

namespace RHTower

theorem universalPositiveForm_thetaNull_iff_canonicalMeasure_support_realDivisor
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative) :
    Q xiThetaSchwartzSource xiThetaSchwartzSource = 0 ↔
      (Q.compactSpectralRieszMeasure hQ hQnonneg).support ⊆ xiRealZeroSet := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  letI : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  have hrep := Q.compactSpectralRieszForm_eq hQ hQnonneg
  change Q xiThetaSchwartzSource xiThetaSchwartzSource = 0 ↔ μ.support ⊆ xiRealZeroSet
  rw [← hrep]
  exact spectralMeasureForm_xiTheta_null_iff_support_realDivisor μ

/-- A theta-null nonnegative momentum-symmetric form has one and only one positive temperate
spectral measure, and that measure is supported on the real `Xi` divisor. -/
theorem existsUnique_temperateSpectralRepresentation_supported_realDivisor_of_thetaNull
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    ∃! μ : Measure ℝ,
      SchwartzMap.TemperateSpectralRepresentation Q μ ∧
        μ.support ⊆ xiRealZeroSet := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  have hμ : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  have hμrep : SchwartzMap.TemperateSpectralRepresentation Q μ :=
    ⟨hμ, (Q.compactSpectralRieszForm_eq hQ hQnonneg).symm⟩
  refine ⟨μ, ⟨hμrep, ?_⟩, ?_⟩
  · exact (universalPositiveForm_thetaNull_iff_canonicalMeasure_support_realDivisor
      Q hQ hQnonneg).mp hnull
  · intro ν hν
    exact (SchwartzMap.existsUnique_temperateSpectralRepresentation Q hQ hQnonneg).unique
      hν.1 hμrep

theorem universalPositiveForm_canonicalMeasure_atomic_of_thetaNull
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    Q.compactSpectralRieszMeasure hQ hQnonneg = Measure.sum
      (fun t : xiRealZeroSet =>
        (Q.compactSpectralRieszMeasure hQ hQnonneg) {(t : ℝ)} •
          Measure.dirac (t : ℝ)) := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  letI : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  have hrep := Q.compactSpectralRieszForm_eq hQ hQnonneg
  have hrep' : SchwartzMap.spectralMeasureForm μ = Q := hrep
  have hspectral : SchwartzMap.spectralMeasureForm μ
      xiThetaSchwartzSource xiThetaSchwartzSource = 0 := by
    exact (congrArg (fun A : SchwartzMap.ContinuousSchwartzSesquilinearForm =>
      A xiThetaSchwartzSource xiThetaSchwartzSource) hrep').trans hnull
  exact spectralMeasure_eq_sum_smul_dirac_xiRealZeroSet_of_null_xiThetaSchwartzSource
    μ hspectral

theorem universalPositiveForm_theta_leftRadical_of_thetaNull
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0)
    (v : SchwartzMap ℝ ℂ) : Q xiThetaSchwartzSource v = 0 := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  letI : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  have hrep := Q.compactSpectralRieszForm_eq hQ hQnonneg
  have hrep' : SchwartzMap.spectralMeasureForm μ = Q := hrep
  have hspectral : SchwartzMap.spectralMeasureForm μ
      xiThetaSchwartzSource xiThetaSchwartzSource = 0 := by
    exact (congrArg (fun A : SchwartzMap.ContinuousSchwartzSesquilinearForm =>
      A xiThetaSchwartzSource xiThetaSchwartzSource) hrep').trans hnull
  rw [← hrep']
  exact spectralMeasureForm_xiTheta_left_eq_zero_of_self_eq_zero μ hspectral v

theorem universalPositiveForm_thetaNull_closable_iff_canonicalMeasure_zero
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 ↔
      Q.compactSpectralRieszMeasure hQ hQnonneg = 0 := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  letI : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  have hrep := Q.compactSpectralRieszForm_eq hQ hQnonneg
  have hrep' : SchwartzMap.spectralMeasureForm μ = Q := hrep
  have hspectral : SchwartzMap.spectralMeasureForm μ
      xiThetaSchwartzSource xiThetaSchwartzSource = 0 := by
    exact (congrArg (fun A : SchwartzMap.ContinuousSchwartzSesquilinearForm =>
      A xiThetaSchwartzSource xiThetaSchwartzSource) hrep').trans hnull
  have hclose : Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 ↔
      (SchwartzMap.spectralMeasureForm μ).IsSequentiallyClosableThrough
        xiThetaSchwartzToL2 := by
    constructor
    · intro h
      exact hrep'.symm ▸ h
    · intro h
      exact hrep' ▸ h
  exact hclose.trans
    (spectralMeasureForm_xiTheta_sequentiallyL2Closable_iff_measure_eq_zero μ hspectral)

theorem universalPositiveForm_identicallyZero_iff_canonicalMeasure_zero
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative) :
    (∀ u v : SchwartzMap ℝ ℂ, Q u v = 0) ↔
      Q.compactSpectralRieszMeasure hQ hQnonneg = 0 := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  letI : μ.HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  have hrep := Q.compactSpectralRieszForm_eq hQ hQnonneg
  have hrep' : SchwartzMap.spectralMeasureForm μ = Q := hrep
  have hzero : (∀ u v : SchwartzMap ℝ ℂ, Q u v = 0) ↔
      (∀ u v : SchwartzMap ℝ ℂ, SchwartzMap.spectralMeasureForm μ u v = 0) := by
    constructor
    · intro h u v
      rw [hrep']
      exact h u v
    · intro h u v
      rw [← hrep']
      exact h u v
  exact hzero.trans (spectralMeasureForm_eq_zero_iff_measure_eq_zero μ)

end RHTower
