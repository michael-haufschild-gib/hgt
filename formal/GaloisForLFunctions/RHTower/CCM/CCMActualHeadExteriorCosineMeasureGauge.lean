import GaloisForLFunctions.RHTower.CCM.CCMActualHeadApertureCosineGaugeQuotient
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFirstContactBoundaryRoughness

/-!
# Exterior finite-measure cosine gauges

A physical aperture annihilates not only individual exterior cosine coordinates and integrable
exterior weights, but cosine transforms of arbitrary finite measures supported beyond aperture
diameter. Consequently the corrected CCM symbol is defined only modulo this signed finite-measure
gauge ideal at quadratic-form level. A pointwise nonnegative representative in every such gauge
class is proved sufficient for RH by evaluating it on the canonical restricted-Weil ground lift.
No existence of these representatives is assumed or claimed here.
-/


open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Cosine transform of a finite measure on lag space. -/
def ccmActualHeadExteriorCosineMeasureGauge (μ : Measure ℝ) (xi : ℝ) : ℝ :=
  ∫ h : ℝ, Real.cos (2 * Real.pi * h * xi) ∂μ

theorem integrable_ccmActualHeadExteriorCosineMeasureJoint
    (f : SoninL2) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (Function.uncurry fun h xi : ℝ =>
      Real.cos (2 * Real.pi * h * xi) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) (μ.prod volume) := by
  let D : ℝ → ℝ := fun xi => ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
  have hD : Integrable D := by
    dsimp only [D]
    exact integrable_norm_sq (fourierUnitary f)
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hmajor : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * D p.2)
      (μ.prod volume) := hone.mul_prod hD
  have hcos : Continuous (fun p : ℝ × ℝ =>
      Real.cos (2 * Real.pi * p.1 * p.2)) := by
    fun_prop
  have hDsnd : AEStronglyMeasurable (fun p : ℝ × ℝ => D p.2)
      (μ.prod volume) :=
    hD.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  apply hmajor.mono' (hcos.aestronglyMeasurable.mul hDsnd)
  filter_upwards with p
  have hD0 : 0 ≤ D p.2 := by dsimp only [D]; positivity
  change |Real.cos (2 * Real.pi * p.1 * p.2) * D p.2| ≤ 1 * D p.2
  rw [abs_mul, abs_of_nonneg hD0]
  exact mul_le_mul_of_nonneg_right
    (Real.abs_cos_le_one (2 * Real.pi * p.1 * p.2)) hD0

theorem integrable_ccmActualHeadExteriorCosineMeasureGauge_mul_density
    (f : SoninL2) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun xi : ℝ =>
      ccmActualHeadExteriorCosineMeasureGauge μ xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  let K : ℝ → ℝ → ℝ := fun h xi =>
    Real.cos (2 * Real.pi * h * xi) *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
  have hK : Integrable (Function.uncurry K) (μ.prod volume) := by
    simpa only [K] using integrable_ccmActualHeadExteriorCosineMeasureJoint f μ
  exact hK.integral_prod_right.congr (Filter.Eventually.of_forall fun xi => by
    change (∫ h : ℝ, K h xi ∂μ) =
      (∫ h : ℝ, Real.cos (2 * Real.pi * h * xi) ∂μ) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
    rw [← MeasureTheory.integral_mul_const])

/-- A finite measure supported beyond aperture diameter is a null spectral gauge. -/
theorem integral_ccmActualHeadExteriorCosineMeasureGauge_mul_density_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ h : ℝ ∂μ, 2 * a.1 ≤ h) :
    (∫ xi : ℝ,
      ccmActualHeadExteriorCosineMeasureGauge μ xi *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = 0 := by
  let K : ℝ → ℝ → ℝ := fun h xi =>
    Real.cos (2 * Real.pi * h * xi) *
      ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2
  have hK : Integrable (Function.uncurry K) (μ.prod volume) := by
    simpa only [K] using
      integrable_ccmActualHeadExteriorCosineMeasureJoint (f : SoninL2) μ
  have hswap := MeasureTheory.integral_integral_swap hK
  calc
    (∫ xi : ℝ,
      ccmActualHeadExteriorCosineMeasureGauge μ xi *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) =
        ∫ xi : ℝ, ∫ h : ℝ, K h xi ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with xi
          unfold ccmActualHeadExteriorCosineMeasureGauge
          rw [← MeasureTheory.integral_mul_const]
    _ = ∫ h : ℝ, (∫ xi : ℝ, K h xi) ∂μ := by
          simpa only using hswap.symm
    _ = ∫ _h : ℝ, (0 : ℝ) ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hμ] with h hh
          simp only [K]
          exact integral_ccmActualHeadCosineSpectralDensity_eq_zero_of_two_aperture_le
            a f hh
    _ = 0 := by simp

theorem integral_ccmActualHeadExteriorCosineMeasureGauge_sub_mul_density_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ h : ℝ ∂μ, 2 * a.1 ≤ h)
    (hν : ∀ᵐ h : ℝ ∂ν, 2 * a.1 ≤ h) :
    (∫ xi : ℝ,
      (ccmActualHeadExteriorCosineMeasureGauge μ xi -
          ccmActualHeadExteriorCosineMeasureGauge ν xi) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = 0 := by
  have hμint := integrable_ccmActualHeadExteriorCosineMeasureGauge_mul_density
    (f : SoninL2) μ
  have hνint := integrable_ccmActualHeadExteriorCosineMeasureGauge_mul_density
    (f : SoninL2) ν
  rw [show (fun xi : ℝ =>
      (ccmActualHeadExteriorCosineMeasureGauge μ xi -
          ccmActualHeadExteriorCosineMeasureGauge ν xi) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) =
      fun xi : ℝ =>
        ccmActualHeadExteriorCosineMeasureGauge μ xi *
          ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 -
        ccmActualHeadExteriorCosineMeasureGauge ν xi *
          ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 by
    funext xi
    ring,
    integral_sub hμint hνint,
    integral_ccmActualHeadExteriorCosineMeasureGauge_mul_density_eq_zero a f μ hμ,
    integral_ccmActualHeadExteriorCosineMeasureGauge_mul_density_eq_zero a f ν hν]
  ring

/-- Corrected CCM symbol after an arbitrary signed finite exterior-measure gauge. -/
def ccmCorrectedExteriorMeasureGaugeRepresentative
    (a : SuzukiPositiveAperture) (μ ν : Measure ℝ) (xi : ℝ) : ℝ :=
  correctedCCMSymbol a.1 (2 * Real.pi * xi) +
    ccmActualHeadExteriorCosineMeasureGauge μ xi -
    ccmActualHeadExteriorCosineMeasureGauge ν xi

theorem integrable_correctedCCMSymbol_mul_actualHeadDensity
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let g := ccmArchimedeanWeightedToL2 u.1
    Integrable (fun xi : ℝ =>
      correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) := by
  let g := ccmArchimedeanWeightedToL2 u.1
  have hgamma : Integrable (fun xi : ℝ =>
      2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖g xi‖ ^ 2) := by
    have hcoe := ccmArchimedeanWeightedToL2_coeFn u.1
    exact (integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1).congr (by
      filter_upwards [hcoe] with xi hxi
      rw [hxi])
  have hcurrent := integrable_polarPrimeStieltjesSymbol_mul_actualHeadDensity a u
  exact (hgamma.add hcurrent).congr (Filter.Eventually.of_forall fun xi => by
    change 2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖g xi‖ ^ 2 +
        polarPrimeStieltjesSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 =
      correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2
    rw [correctedCCMSymbol, ccmArchimedeanMultiplier_eq_two_gammaHardyPhaseRate]
    ring)

theorem ccmRestrictedWeilSourceQuadratic_eq_correctedExteriorMeasureGaugeRepresentative
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ h : ℝ ∂μ, 2 * a.1 ≤ h)
    (hν : ∀ᵐ h : ℝ ∂ν, 2 * a.1 ≤ h) :
    let g := ccmArchimedeanWeightedToL2 u.1
    ccmRestrictedWeilSourceQuadratic a u =
      ∫ xi : ℝ, ccmCorrectedExteriorMeasureGaugeRepresentative a μ ν xi *
        ‖g xi‖ ^ 2 := by
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanWeightedToL2 u.1
  have hfourier : fourierUnitary (f : SoninL2) = g := by
    dsimp only [f, g]
    rw [ccmArchimedeanFormToAperture_val_eq_fourierUnitary_symm,
      fourierUnitary.apply_symm_apply]
  have hμzero :=
    integral_ccmActualHeadExteriorCosineMeasureGauge_mul_density_eq_zero a f μ hμ
  have hνzero :=
    integral_ccmActualHeadExteriorCosineMeasureGauge_mul_density_eq_zero a f ν hν
  have hμint := integrable_ccmActualHeadExteriorCosineMeasureGauge_mul_density
    (f : SoninL2) μ
  have hνint := integrable_ccmActualHeadExteriorCosineMeasureGauge_mul_density
    (f : SoninL2) ν
  rw [hfourier] at hμzero hνzero hμint hνint
  have hcorr := integrable_correctedCCMSymbol_mul_actualHeadDensity a u
  have hcoherent := ccmActualHeadCoherentCompletedGammaProducer_eq_sourceQuadratic a u
  unfold ccmActualHeadCoherentCompletedGammaProducer at hcoherent
  change Integrable (fun xi : ℝ =>
    correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) at hcorr
  change (∫ xi : ℝ,
      correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) =
    ccmRestrictedWeilSourceQuadratic a u at hcoherent
  dsimp only [g] at ⊢
  calc
    ccmRestrictedWeilSourceQuadratic a u =
        ∫ xi : ℝ, correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 :=
      hcoherent.symm
    _ = (∫ xi : ℝ,
          correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) +
        (∫ xi : ℝ,
          ccmActualHeadExteriorCosineMeasureGauge μ xi * ‖g xi‖ ^ 2) -
        (∫ xi : ℝ,
          ccmActualHeadExteriorCosineMeasureGauge ν xi * ‖g xi‖ ^ 2) := by
      rw [hμzero, hνzero]
      ring
    _ = ∫ xi : ℝ,
        (correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 +
          ccmActualHeadExteriorCosineMeasureGauge μ xi * ‖g xi‖ ^ 2) -
          ccmActualHeadExteriorCosineMeasureGauge ν xi * ‖g xi‖ ^ 2 := by
      have hadd := integral_add hcorr hμint
      have hsub := integral_sub (hcorr.add hμint) hνint
      calc
        (∫ xi : ℝ,
            correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) +
            (∫ xi : ℝ,
              ccmActualHeadExteriorCosineMeasureGauge μ xi * ‖g xi‖ ^ 2) -
            (∫ xi : ℝ,
              ccmActualHeadExteriorCosineMeasureGauge ν xi * ‖g xi‖ ^ 2) =
          (∫ xi : ℝ,
            correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 +
              ccmActualHeadExteriorCosineMeasureGauge μ xi * ‖g xi‖ ^ 2) -
            (∫ xi : ℝ,
              ccmActualHeadExteriorCosineMeasureGauge ν xi * ‖g xi‖ ^ 2) := by
          rw [hadd]
        _ = ∫ xi : ℝ,
            (correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 +
              ccmActualHeadExteriorCosineMeasureGauge μ xi * ‖g xi‖ ^ 2) -
              ccmActualHeadExteriorCosineMeasureGauge ν xi * ‖g xi‖ ^ 2 :=
          hsub.symm
    _ = ∫ xi : ℝ, ccmCorrectedExteriorMeasureGaugeRepresentative a μ ν xi *
          ‖g xi‖ ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with xi
      unfold ccmCorrectedExteriorMeasureGaugeRepresentative
      ring

theorem ccmRestrictedWeilSourceQuadratic_nonneg_of_correctedExteriorMeasureGaugeRepresentative
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ h : ℝ ∂μ, 2 * a.1 ≤ h)
    (hν : ∀ᵐ h : ℝ ∂ν, 2 * a.1 ≤ h)
    (hrep : ∀ xi : ℝ, 0 ≤ ccmCorrectedExteriorMeasureGaugeRepresentative a μ ν xi) :
    0 ≤ ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_correctedExteriorMeasureGaugeRepresentative
    a u μ ν hμ hν]
  apply integral_nonneg
  intro xi
  exact mul_nonneg (hrep xi) (sq_nonneg _)

/-- A pointwise-positive representative in every exterior-measure gauge class is sufficient for
RH.  This theorem isolates the remaining construction problem without assuming source positivity. -/
theorem riemannHypothesis_of_exists_nonnegative_correctedExteriorMeasureGaugeRepresentative
    (hrep : ∀ a : SuzukiPositiveAperture,
      ∃ μ ν : FiniteMeasure ℝ,
        (∀ᵐ h : ℝ ∂(μ : Measure ℝ), 2 * a.1 ≤ h) ∧
        (∀ᵐ h : ℝ ∂(ν : Measure ℝ), 2 * a.1 ≤ h) ∧
        ∀ xi : ℝ,
          0 ≤ ccmCorrectedExteriorMeasureGaugeRepresentative a μ ν xi) :
    RiemannHypothesis := by
  by_contra hnot
  obtain ⟨a, henergy⟩ :=
    exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hnot
  obtain ⟨μ, ν, hμ, hν, hpositive⟩ := hrep a
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  have hsource : 0 ≤ ccmRestrictedWeilSourceQuadratic a u :=
    ccmRestrictedWeilSourceQuadratic_nonneg_of_correctedExteriorMeasureGaugeRepresentative
      a u (μ : Measure ℝ) (ν : Measure ℝ) hμ hν hpositive
  have hground := ccmRestrictedWeilCanonicalGroundFormLift_source a
  have hnorm : 0 <
      ‖(ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr
      (ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a))
  dsimp only [u] at hsource
  rw [hground] at hsource
  nlinarith

end RHTower

