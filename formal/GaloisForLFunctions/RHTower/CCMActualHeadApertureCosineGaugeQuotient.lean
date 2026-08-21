import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileEndpointGauge

/-!
# Aperture cosine-gauge quotient

A physical head supported in the aperture annihilates every spectral cosine coordinate at or beyond
the diameter. Fubini upgrades this pointwise lag law to an infinite-dimensional gauge ideal: the
cosine transform of any integrable exterior weight has zero quadratic average. The decaying
first-Binet exterior tail is a canonical member of this ideal. The final theorems identify the
phase-coherent corrected CCM average, and its RH-bearing canonical-head sign condition, with the
endpoint-free outgoing quantile representative.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Every spectral cosine coordinate at or beyond the physical diameter is quadratically null. -/
theorem integral_ccmActualHeadCosineSpectralDensity_eq_zero_of_two_aperture_le
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {h : ℝ} (hh : 2 * a.1 ≤ h) :
    (∫ xi : ℝ,
      Real.cos (2 * Real.pi * h * xi) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = 0 := by
  let g : SoninL2 := fourierUnitary (f : SoninL2)
  have hfg : fourierUnitary.symm g = (f : SoninL2) := by
    dsimp only [g]
    exact fourierUnitary.symm_apply_apply (f : SoninL2)
  have hspectral := ccmActualHeadSymmetricAutocorrelation_fourierUnitary_symm h g
  rw [hfg, ccmActualHeadSymmetricAutocorrelation_eq_zero_of_two_aperture_le a f hh]
    at hspectral
  simpa only [g] using hspectral.symm

/-- Cosine transform of an arbitrary integrable weight on the exterior aperture ray. -/
def ccmActualHeadExteriorCosineGauge
    (a : SuzukiPositiveAperture) (w : ℝ → ℝ) (xi : ℝ) : ℝ :=
  ∫ h in Ici (2 * a.1), w h * Real.cos (2 * Real.pi * h * xi)

/-- Absolute product integrability needed to exchange exterior lag and spectral frequency. -/
theorem integrable_ccmActualHeadExteriorCosineJoint
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (w : ℝ → ℝ) (hw : IntegrableOn w (Ici (2 * a.1))) :
    Integrable (Function.uncurry fun h xi : ℝ =>
      w h * Real.cos (2 * Real.pi * h * xi) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2)
      ((volume.restrict (Ici (2 * a.1))).prod volume) := by
  let g : ℝ → ℂ := (fourierUnitary (f : SoninL2) : ℝ → ℂ)
  let D : ℝ → ℝ := fun xi => ‖g xi‖ ^ 2
  have hD : Integrable D := by
    dsimp only [D, g]
    exact integrable_norm_sq (fourierUnitary (f : SoninL2))
  have hmajor : Integrable (fun p : ℝ × ℝ => ‖w p.1‖ * D p.2)
      ((volume.restrict (Ici (2 * a.1))).prod volume) :=
    hw.norm.mul_prod hD
  have hwfst : AEStronglyMeasurable (fun p : ℝ × ℝ => w p.1)
      ((volume.restrict (Ici (2 * a.1))).prod volume) :=
    hw.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst
  have hcos : Continuous (fun p : ℝ × ℝ =>
      Real.cos (2 * Real.pi * p.1 * p.2)) := by
    fun_prop
  have hDsnd : AEStronglyMeasurable (fun p : ℝ × ℝ => D p.2)
      ((volume.restrict (Ici (2 * a.1))).prod volume) :=
    hD.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  apply hmajor.mono'
    ((hwfst.mul hcos.aestronglyMeasurable).mul hDsnd)
  filter_upwards with p
  have hD0 : 0 ≤ D p.2 := by dsimp only [D]; positivity
  change |w p.1 * Real.cos (2 * Real.pi * p.1 * p.2) * D p.2| ≤
    ‖w p.1‖ * D p.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hD0,
    ← Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg (w p.1))
      (by simpa [Real.norm_eq_abs] using
        Real.abs_cos_le_one (2 * Real.pi * p.1 * p.2))) hD0

theorem integrable_ccmActualHeadExteriorCosineGauge_mul_density
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (w : ℝ → ℝ) (hw : IntegrableOn w (Ici (2 * a.1))) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadExteriorCosineGauge a w xi *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) := by
  let K : ℝ → ℝ → ℝ := fun h xi =>
    w h * Real.cos (2 * Real.pi * h * xi) *
      ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2
  have hK : Integrable (Function.uncurry K)
      ((volume.restrict (Ici (2 * a.1))).prod volume) := by
    simpa only [K] using integrable_ccmActualHeadExteriorCosineJoint a f w hw
  exact hK.integral_prod_right.congr (Filter.Eventually.of_forall fun xi => by
    change (∫ h in Ici (2 * a.1), K h xi) =
      (∫ h in Ici (2 * a.1), w h * Real.cos (2 * Real.pi * h * xi)) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2
    rw [← MeasureTheory.integral_mul_const])

/-- Entire exterior cosine transforms vanish in the aperture quadratic quotient. -/
theorem integral_ccmActualHeadExteriorCosineGauge_mul_density_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (w : ℝ → ℝ) (hw : IntegrableOn w (Ici (2 * a.1))) :
    (∫ xi : ℝ,
      ccmActualHeadExteriorCosineGauge a w xi *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = 0 := by
  let K : ℝ → ℝ → ℝ := fun h xi =>
    w h * Real.cos (2 * Real.pi * h * xi) *
      ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2
  have hK : Integrable (Function.uncurry K)
      ((volume.restrict (Ici (2 * a.1))).prod volume) := by
    simpa only [K] using integrable_ccmActualHeadExteriorCosineJoint a f w hw
  have hswap := MeasureTheory.integral_integral_swap hK
  calc
    (∫ xi : ℝ,
      ccmActualHeadExteriorCosineGauge a w xi *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) =
        ∫ xi : ℝ, ∫ h in Ici (2 * a.1), K h xi := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with xi
          unfold ccmActualHeadExteriorCosineGauge
          rw [← MeasureTheory.integral_mul_const]
    _ = ∫ h in Ici (2 * a.1), ∫ xi : ℝ, K h xi := hswap.symm
    _ = ∫ h in Ici (2 * a.1), 0 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ici] with h hh
          simp only [K]
          rw [show (fun xi : ℝ =>
              w h * Real.cos (2 * Real.pi * h * xi) *
                ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) =
              fun xi : ℝ => w h *
                (Real.cos (2 * Real.pi * h * xi) *
                  ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) by
            funext xi
            ring]
          rw [MeasureTheory.integral_const_mul,
            integral_ccmActualHeadCosineSpectralDensity_eq_zero_of_two_aperture_le
              a f hh, mul_zero]
    _ = 0 := by simp

/-- Exterior decaying first-Binet polar half. -/
def ccmActualHeadExteriorFirstBinetCosineGauge
    (a : SuzukiPositiveAperture) (xi : ℝ) : ℝ :=
  ccmActualHeadExteriorCosineGauge a
    (fun h => 2 * ccmGammaFirstBinetModeWeight h) xi

theorem integrableOn_two_mul_ccmGammaFirstBinetModeWeight_Ici
    (a : SuzukiPositiveAperture) :
    IntegrableOn (fun h : ℝ => 2 * ccmGammaFirstBinetModeWeight h)
      (Ici (2 * a.1)) := by
  have hexp : IntegrableOn (fun h : ℝ => Real.exp (-(1 / 2 : ℝ) * h))
      (Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi (b := (1 / 2 : ℝ)) (0 : ℝ) (by norm_num)
  have hsub : Ici (2 * a.1) ⊆ Ioi (0 : ℝ) := by
    intro h hh
    exact lt_of_lt_of_le (mul_pos (by norm_num) a.property) hh
  exact ((hexp.mono_set hsub).const_mul 2).congr
    (Filter.Eventually.of_forall fun h => by
      unfold ccmGammaFirstBinetModeWeight
      change 2 * Real.exp (-(1 / 2 : ℝ) * h) = 2 * Real.exp (-(h / 2))
      rw [show -(h / 2) = -(1 / 2 : ℝ) * h by ring])

theorem integral_ccmActualHeadExteriorFirstBinetCosineGauge_mul_density_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (∫ xi : ℝ,
      ccmActualHeadExteriorFirstBinetCosineGauge a xi *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = 0 := by
  unfold ccmActualHeadExteriorFirstBinetCosineGauge
  exact integral_ccmActualHeadExteriorCosineGauge_mul_density_eq_zero a f _
    (integrableOn_two_mul_ccmGammaFirstBinetModeWeight_Ici a)

/-- The phase-coherent corrected CCM average is exactly the endpoint-free outgoing quantile
representative. The preceding exterior-gauge theorem supplies the support-geometric quotient
mechanism behind the first-Binet cancellation. -/
theorem ccmActualHeadCoherentCompletedGammaProducer_eq_endpointFreeOutgoingQuantile
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    ccmActualHeadCoherentCompletedGammaProducer a u =
      2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        4 * ‖f‖ ^ 2 +
        2 * ∫ xi : ℝ,
          ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi *
            ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 := by
  rw [ccmActualHeadCoherentCompletedGammaProducer_eq_sourceQuadratic,
    ← ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_sourceQuadratic]
  exact
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_endpointFreeCosinePhaseSymbol a u

/-- RH-bearing finite-head condition in the aperture cosine-gauge quotient. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_endpointFreeOutgoingQuantile_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    let u := ccmRestrictedWeilCanonicalGroundHead a n
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ 2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        4 * ‖f‖ ^ 2 +
        2 * ∫ xi : ℝ,
          ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi *
            ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_coherentCompletedGamma_nonneg,
    ccmActualHeadCoherentCompletedGammaProducer_eq_endpointFreeOutgoingQuantile]

end RHTower
