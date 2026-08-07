import GaloisForLFunctions.RHTower.HedenmalmThetaSquaredSeamPencil
import GaloisForLFunctions.RHTower.HedenmalmRootFluxModularCharge
import GaloisForLFunctions.RHTower.HedenmalmThetaRootMomentNormalization

/-!
# The thermal RH energy as compact theta boundary flux

The faithful reciprocal-square orientation energy is identified term by term with the square of
the canonically normalized boundary flux of the actual theta root mode.  A second identity places
that flux on the genuine nonzero eigenvector of the fixed compact theta source inverse.
-/

open Complex MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmThetaSource HedenmalmHilbertSchmidt

/-- The abstract compact theta divisor vector is almost everywhere the explicit quantile root
mode with its exact source-mass normalization. -/
theorem thetaDivisorEigenvector_ae_rootG (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    (thetaDivisorEigenvector z hz hzero : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => (Real.sqrt thetaSource.mass : ℂ) * rootG thetaSource z t := by
  let v : SourceSpace thetaSource := thetaDivisorSourceVector z hz hzero
  have hunit := quantileUnitary_ae thetaSource v
  have hvq := thetaDivisorSourceVector_quantile_ae z hz hzero
  filter_upwards [hunit, hvq, ae_unitIntervalMeasure_mem_Ioo] with t hu hv ht
  change (quantileUnitary thetaSource v : ℝ → ℂ) t = _
  rw [hu, hv]
  simpa only [quantileTransform] using
    (quantileTransform_sourceModeF_eq_rootG (z := z) ht)

/-- Exact monopole of the compact theta divisor eigenvector. -/
theorem pinnedMean_thetaDivisorEigenvector (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    pinnedMean (thetaDivisorEigenvector z hz hzero) =
      (Real.sqrt thetaSource.mass : ℂ) := by
  rw [pinnedMean,
    integral_congr_ae (thetaDivisorEigenvector_ae_rootG z hz hzero),
    unitIntervalMeasure_eq, MeasureTheory.integral_const_mul,
    integral_rootG_thetaSource_eq_one hz hzero, mul_one]

/-- Exact centered dipole of the compact theta divisor eigenvector. -/
theorem pinnedCentered_thetaDivisorEigenvector (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    pinnedCentered (thetaDivisorEigenvector z hz hzero) =
      (Real.sqrt thetaSource.mass : ℂ) *
        (∫ t in Ioo (0 : ℝ) 1,
          (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t) := by
  let g : H := thetaDivisorEigenvector z hz hzero
  have hroot := thetaDivisorEigenvector_ae_rootG z hz hzero
  have hcenter :
      (fun t : ℝ => (t : ℂ) * g t - (1 / 2 : ℂ) * g t)
        =ᵐ[unitIntervalMeasure]
      (fun t : ℝ => (Real.sqrt thetaSource.mass : ℂ) *
        (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t) := by
    filter_upwards [hroot] with t ht
    dsimp only [g] at ht ⊢
    rw [ht]
    ring
  rw [pinnedCentered, pinnedFirstMoment, pinnedMean,
    ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_sub (integrable_coordinate_mul g)
      ((integrable_coe g).const_mul (1 / 2 : ℂ)),
    integral_congr_ae hcenter, unitIntervalMeasure_eq]
  simpa only [mul_assoc] using
    (MeasureTheory.integral_const_mul
      (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (Real.sqrt thetaSource.mass : ℂ)
      (fun t : ℝ => (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t))

/-- The rank-two boundary form evaluated on the genuine compact theta divisor eigenvector. -/
theorem inner_pinnedBoundaryCLM_thetaDivisorEigenvector
    (z : ℂ) (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    (inner ℂ (pinnedBoundaryCLM (thetaDivisorEigenvector z hz hzero))
      (thetaDivisorEigenvector z hz hzero) : ℂ) =
      (thetaSource.mass : ℂ) *
        Complex.ofReal (2 * z.im * thetaRootEnergy z) := by
  let c : ℂ := ∫ t in Ioo (0 : ℝ) 1,
    (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t
  have hpair :
      -(c + (starRingEnd ℂ) c) =
        Complex.ofReal (2 * z.im * thetaRootEnergy z) := by
    simpa only [c, integral_rootG_thetaSource_eq_one hz hzero, map_one,
      one_mul, mul_one, zero_sub, thetaRootEnergy] using
      (rootBoundaryMomentPairing_thetaSource hz hzero)
  have hsq : (Real.sqrt thetaSource.mass : ℂ) *
      (Real.sqrt thetaSource.mass : ℂ) = (thetaSource.mass : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt thetaSource.mass_pos.le]
  rw [inner_pinnedBoundaryCLM_eq,
    pinnedMean_thetaDivisorEigenvector z hz hzero,
    pinnedCentered_thetaDivisorEigenvector z hz hzero]
  rw [map_mul, Complex.conj_ofReal]
  calc
    -((Real.sqrt thetaSource.mass : ℂ) *
          ((Real.sqrt thetaSource.mass : ℂ) * c) +
        (Real.sqrt thetaSource.mass : ℂ) * (starRingEnd ℂ) c *
          (Real.sqrt thetaSource.mass : ℂ)) =
        (thetaSource.mass : ℂ) * (-(c + (starRingEnd ℂ) c)) := by
          rw [← hsq]
          ring
    _ = (thetaSource.mass : ℂ) *
        Complex.ofReal (2 * z.im * thetaRootEnergy z) := by rw [hpair]

/-- Ordered root flux attached to one multiplicity-exact Xi divisor copy. -/
def thetaXiRootFlux (q : XiZeroCopy) : ℝ :=
  (∫ t in Ioo (0 : ℝ) 1,
    -(rootH thetaSource (xiSpectralPoint q) t)).re

/-- The positive root energy attached to the same divisor copy. -/
def thetaXiRootEnergy (q : XiZeroCopy) : ℝ :=
  thetaRootEnergy (xiSpectralPoint q)

theorem thetaXiRootEnergy_pos (q : XiZeroCopy) :
    0 < thetaXiRootEnergy q := by
  exact thetaRootEnergy_pos (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- The root flux reads the transverse spectral coordinate without loss. -/
theorem thetaXiRootFlux_eq (q : XiZeroCopy) :
    thetaXiRootFlux q =
      -(xiSpectralPoint q).im * thetaXiRootEnergy q := by
  exact rootFlux_identity_thetaSource
    (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- Real boundary quadratic output of the actual compact theta eigenvector. -/
def thetaXiRankTwoBoundaryFlux (q : XiZeroCopy) : ℝ :=
  (inner ℂ (pinnedBoundaryCLM (thetaXiDivisorEigenvector q))
    (thetaXiDivisorEigenvector q)).re

/-- The compact-eigenvector boundary flux reads the transverse coordinate with a strictly positive
weight. -/
theorem thetaXiRankTwoBoundaryFlux_eq (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q =
      2 * thetaSource.mass * (xiSpectralPoint q).im * thetaXiRootEnergy q := by
  rw [thetaXiRankTwoBoundaryFlux, thetaXiDivisorEigenvector,
    inner_pinnedBoundaryCLM_thetaDivisorEigenvector
      (xiSpectralPoint q) (thetaXiSpectralPoint_mem_sourceStrip q)
      (xiC_thetaSource_xiSpectralPoint_eq_zero q)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, thetaXiRootEnergy]
  ring

/-- The boundary quadratic form and root primitive give the same oriented flux, including the
source-mass normalization. -/
theorem thetaXiRankTwoBoundaryFlux_eq_rootFlux (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q =
      -2 * thetaSource.mass * thetaXiRootFlux q := by
  rw [thetaXiRankTwoBoundaryFlux_eq, thetaXiRootFlux_eq]
  ring

/-- One theorem packages both facts needed downstream: the mode is a genuine eigenvector of the
fixed compact source inverse and its boundary form detects exactly its nonreal displacement. -/
theorem thetaXiRankTwoBoundaryFlux_eigenmode (q : XiZeroCopy) :
    thetaCompactSourceInverse (thetaXiDivisorEigenvector q) =
        thetaXiReciprocalEigenvalue q • thetaXiDivisorEigenvector q ∧
      thetaXiRankTwoBoundaryFlux q =
        2 * thetaSource.mass * (xiSpectralPoint q).im * thetaXiRootEnergy q :=
  ⟨thetaCompactSourceInverse_thetaXi_eigen q, thetaXiRankTwoBoundaryFlux_eq q⟩

/-- Imaginary reciprocal square in centered spectral coordinates. -/
theorem xiZeroCopyReciprocalSquare_im_eq_spectral (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im =
      -(2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im) /
        Complex.normSq (xiSpectralPoint q) ^ 2 := by
  rw [xiZeroCopyReciprocalSquare, pow_two]
  simp only [Complex.mul_im, Complex.inv_re, Complex.inv_im]
  ring

/-- Canonically normalized squared output of the theta root-flux observer. -/
def thetaXiNormalizedRootFluxTerm (q : XiZeroCopy) : ℝ :=
  (2 * (xiSpectralPoint q).re * thetaXiRootFlux q /
      (thetaXiRootEnergy q * Complex.normSq (xiSpectralPoint q) ^ 2)) ^ 2

/-- **Pointwise Frankenstein identity.**  The normalized theta flux is exactly the faithful
reciprocal-square transverse square. -/
theorem thetaXiNormalizedRootFluxTerm_eq (q : XiZeroCopy) :
    thetaXiNormalizedRootFluxTerm q =
      (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  have hE : thetaXiRootEnergy q ≠ 0 := (thetaXiRootEnergy_pos q).ne'
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [thetaXiNormalizedRootFluxTerm, thetaXiRootFlux_eq,
    xiZeroCopyReciprocalSquare_im_eq_spectral]
  field_simp [hE, hD]

/-- Canonically normalized squared boundary output of the genuine compact theta eigenvector. -/
def thetaXiNormalizedRankTwoBoundaryFluxTerm (q : XiZeroCopy) : ℝ :=
  ((xiSpectralPoint q).re * thetaXiRankTwoBoundaryFlux q /
      (thetaSource.mass * thetaXiRootEnergy q *
        Complex.normSq (xiSpectralPoint q) ^ 2)) ^ 2

/-- The normalized compact-eigenvector boundary output is exactly the faithful reciprocal-square
transverse atom. -/
theorem thetaXiNormalizedRankTwoBoundaryFluxTerm_eq (q : XiZeroCopy) :
    thetaXiNormalizedRankTwoBoundaryFluxTerm q =
      (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  have hM : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
  have hE : thetaXiRootEnergy q ≠ 0 := (thetaXiRootEnergy_pos q).ne'
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [thetaXiNormalizedRankTwoBoundaryFluxTerm,
    thetaXiRankTwoBoundaryFlux_eq,
    xiZeroCopyReciprocalSquare_im_eq_spectral]
  field_simp [hM, hE, hD]

/-- Global compact-root flux energy. -/
def thetaXiNormalizedRootFluxEnergy : ℝ :=
  ∑' q : XiZeroCopy, thetaXiNormalizedRootFluxTerm q

theorem summable_thetaXiNormalizedRootFluxTerm :
    Summable thetaXiNormalizedRootFluxTerm :=
  summable_xiThermalOrientationTerm.congr fun q =>
    (thetaXiNormalizedRootFluxTerm_eq q).symm

/-- The new theta flux energy is exactly the established faithful thermal orientation energy. -/
theorem thetaXiNormalizedRootFluxEnergy_eq_thermalOrientationEnergy :
    thetaXiNormalizedRootFluxEnergy = xiThermalOrientationEnergy := by
  rw [thetaXiNormalizedRootFluxEnergy, xiThermalOrientationEnergy]
  exact tsum_congr thetaXiNormalizedRootFluxTerm_eq

theorem thetaXiNormalizedRootFluxEnergy_nonneg :
    0 ≤ thetaXiNormalizedRootFluxEnergy := by
  rw [thetaXiNormalizedRootFluxEnergy]
  exact tsum_nonneg fun q => sq_nonneg _

/-- Vanishing of the compact theta root-flux energy is exactly RH. -/
theorem thetaXiNormalizedRootFluxEnergy_eq_zero_iff_riemannHypothesis :
    thetaXiNormalizedRootFluxEnergy = 0 ↔ RiemannHypothesis := by
  rw [thetaXiNormalizedRootFluxEnergy_eq_thermalOrientationEnergy,
    xiThermalOrientationEnergy_eq_zero_iff_rh]

/-- Global normalized boundary energy of the genuine compact theta divisor eigenvectors. -/
def thetaXiNormalizedRankTwoBoundaryFluxEnergy : ℝ :=
  ∑' q : XiZeroCopy, thetaXiNormalizedRankTwoBoundaryFluxTerm q

theorem summable_thetaXiNormalizedRankTwoBoundaryFluxTerm :
    Summable thetaXiNormalizedRankTwoBoundaryFluxTerm :=
  summable_xiThermalOrientationTerm.congr fun q =>
    (thetaXiNormalizedRankTwoBoundaryFluxTerm_eq q).symm

/-- The actual compact-eigenvector boundary energy is the faithful thermal orientation energy. -/
theorem thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_thermalOrientationEnergy :
    thetaXiNormalizedRankTwoBoundaryFluxEnergy = xiThermalOrientationEnergy := by
  rw [thetaXiNormalizedRankTwoBoundaryFluxEnergy, xiThermalOrientationEnergy]
  exact tsum_congr thetaXiNormalizedRankTwoBoundaryFluxTerm_eq

theorem thetaXiNormalizedRankTwoBoundaryFluxEnergy_nonneg :
    0 ≤ thetaXiNormalizedRankTwoBoundaryFluxEnergy := by
  rw [thetaXiNormalizedRankTwoBoundaryFluxEnergy]
  exact tsum_nonneg fun q => sq_nonneg _

/-- **Compact boundary-flux RH criterion.** RH is equivalent to vanishing of the normalized
boundary quadratic outputs of all genuine eigenvectors of the fixed compact theta source inverse. -/
theorem thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_zero_iff_riemannHypothesis :
    thetaXiNormalizedRankTwoBoundaryFluxEnergy = 0 ↔ RiemannHypothesis := by
  rw [thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_thermalOrientationEnergy,
    xiThermalOrientationEnergy_eq_zero_iff_rh]

end

end RHTower
