import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxWeilParitySchwarzPairLorentzWeld
import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherGlobalClassLawProducer
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeTranslationCompletedRadialWorkEquivalence
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalSourceWeylRenewal
import GaloisForLFunctions.RHTower.XiShiftedHankelFarRightPositiveDefinite

/-!
# Source-normal certificate/receiver phase of the Schwarz-pair Lorentz decomposition

The Lorentz source-normal coefficient admits one actual fixed-source realization and one nonlinear
receiver coordinate.

At zero normal charge, an actual fixed abelian class law carries the complete adaptive Fisher
scale orbit.  Conversely, cofinal contiguity forbids that fixed-law orbit at every nonzero normal
charge.  Thus certificate existence is exactly the zero fibre of the Schwarz-pair normal channel.

Off the zero fibre, the shifted-Xi terminal-source Weyl aggregate can be evaluated at a purely
imaginary aperture chosen to have the absolute centered spectral displacement.  At every finite
degree, unconditional far-right Hankel positivity then admits a nonlinear Jacobi renewal whose
normalized increment returns that chosen aperture height.  After analytic-multiplicity and
reciprocal-metric scaling, the fitted value is precisely the Schwarz-pair normal coefficient.

The resulting formal phase dichotomy separates fixed-source contiguity from changing-admission
receiver geometry.  It does not by itself exert source-native vanishing pressure: the aperture is
external data.  The later universality no-go makes that limitation exact.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Purely imaginary Weyl aperture whose height is the Schwarz-pair normal displacement. -/
def xiSchwarzPairSourceNormalAperture (q : XiZeroCopy) : ℂ :=
  ((|(xiSpectralPoint q).im| : ℝ) : ℂ) * Complex.I

@[simp] theorem xiSchwarzPairSourceNormalAperture_im (q : XiZeroCopy) :
    (xiSchwarzPairSourceNormalAperture q).im = |(xiSpectralPoint q).im| := by
  simp [xiSchwarzPairSourceNormalAperture]

/-- Fixed abelian class-law scale-orbit certificates exist exactly on the zero fibre of the
Lorentz source-normal channel. -/
theorem sourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate_nonempty_iff_normalCoefficient_eq_zero
    (q : XiZeroCopy) (p : Nat.Primes) {d : ℝ} (hd : 1 < d) :
    Nonempty (SourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate q p d) ↔
      xiSchwarzPairSourceNormalCoefficient q = 0 := by
  change Nonempty (SourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate p d
      (primeDepthBVWoldXiCenteredRate q.1)) ↔ _
  rw [sourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate_nonempty_iff p hd,
    HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_eq_neg_two_mul_spectral_im,
    xiSchwarzPairSourceNormalCoefficient_eq_zero_iff]
  constructor <;> intro h
  · linarith
  · rw [h]
    norm_num

/-- Source-normal rate is the absolute adaptive Fisher centered rate in reciprocal spectral
metric. -/
theorem xiSchwarzPairSourceNormalRate_eq_abs_centeredRate_div_normSq (q : XiZeroCopy) :
    xiSchwarzPairSourceNormalRate q =
      |primeDepthBVWoldXiCenteredRate q.1| /
        Complex.normSq (xiSpectralPoint q) := by
  rw [xiSchwarzPairSourceNormalRate_eq,
    HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_eq_neg_two_mul_spectral_im]
  simp [abs_mul]

/-- Reciprocal metric removes the denominator from the normal coefficient and leaves analytic
multiplicity times absolute centered rate. -/
theorem normSq_mul_xiSchwarzPairSourceNormalCoefficient_eq_multiplicity_mul_abs_centeredRate
    (q : XiZeroCopy) :
    Complex.normSq (xiSpectralPoint q) * xiSchwarzPairSourceNormalCoefficient q =
      xiSchwarzPairAnalyticMultiplicity q *
        |primeDepthBVWoldXiCenteredRate q.1| := by
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [xiSchwarzPairSourceNormalCoefficient,
    xiSchwarzPairSourceNormalRate_eq_abs_centeredRate_div_normSq]
  field_simp

/-- Normalized nonlinear receiver increment in the shifted-Xi terminal Weyl degree renewal. -/
def xiSchwarzPairCompletedSourceWeylNormalizedIncrement
    (q : XiZeroCopy) (w : ℝ) (n : ℕ) : ℝ :=
  let z := xiSchwarzPairSourceNormalAperture q
  let Wnext := xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w (n + 1) z
  let Wcurrent := xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w n z
  (-Wnext.im) / Complex.normSq Wnext -
    HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n * (-Wcurrent.im)

/-- Inside any positive admission block, nonlinear Weyl renewal returns the chosen source-normal
aperture height. -/
theorem xiSchwarzPairCompletedSourceWeylNormalizedIncrement_eq_normalDisplacement
    (q : XiZeroCopy) {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef)
    (him : (xiSpectralPoint q).im ≠ 0) :
    xiSchwarzPairCompletedSourceWeylNormalizedIncrement q w n =
      |(xiSpectralPoint q).im| := by
  have hz : 0 < (xiSchwarzPairSourceNormalAperture q).im := by
    simpa using abs_pos.mpr him
  simpa only [xiSchwarzPairCompletedSourceWeylNormalizedIncrement,
    xiSchwarzPairSourceNormalAperture_im] using
    xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex_normalized_increment
      hn hH hz

/-- Every off-line Xi copy has, at each finite degree, an unconditionally admitted nonlinear Weyl
receiver fitted to its multiplicity-weighted Lorentz normal coefficient. -/
theorem xiSchwarzPair_offLine_finiteDegree_nonlinearRenewal
    (q : XiZeroCopy) (him : (xiSpectralPoint q).im ≠ 0) {n : ℕ} (hn : 0 < n) :
    ∃ w : ℝ, 1 < w ∧
      (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 3)).PosDef ∧
      xiSchwarzPairCompletedSourceWeylNormalizedIncrement q w n =
        |(xiSpectralPoint q).im| ∧
      2 * xiSchwarzPairAnalyticMultiplicity q *
          xiSchwarzPairCompletedSourceWeylNormalizedIncrement q w n =
        Complex.normSq (xiSpectralPoint q) *
          xiSchwarzPairSourceNormalCoefficient q := by
  have hev : ∀ᶠ w : ℝ in atTop,
      (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 3)).PosDef ∧ 1 < w :=
    (xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 3)).and
      (eventually_gt_atTop 1)
  obtain ⟨w, hHw, hw⟩ := hev.exists
  have hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef := by
    have heq : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 3) =
        HTGeometry.momentHankelMatrix
          (xiShiftedRealMomentSequence w) (n + 3) := by
      ext i j
      rfl
    rw [← heq]
    exact hHw
  have hinc := xiSchwarzPairCompletedSourceWeylNormalizedIncrement_eq_normalDisplacement
    q hn hH him
  refine ⟨w, hw, hH, hinc, ?_⟩
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [hinc, xiSchwarzPairSourceNormalCoefficient,
    xiSchwarzPairSourceNormalRate_eq]
  field_simp

/-- Closed certificate/receiver dichotomy: a Xi copy either lies in the fixed-law neutral
certificate phase, or every finite degree admits a positive fitted nonlinear receiver value. -/
theorem xiSchwarzPair_classLaw_or_nonlinearRenewalPhase
    (q : XiZeroCopy) (p : Nat.Primes) {d : ℝ} (hd : 1 < d) :
    Nonempty (SourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate q p d) ∨
      (∀ n : ℕ, 0 < n → ∃ w : ℝ, 1 < w ∧
        (HTGeometry.momentHankelMatrix
          (xiShiftedRealMomentSequence w) (n + 3)).PosDef ∧
        xiSchwarzPairCompletedSourceWeylNormalizedIncrement q w n =
          |(xiSpectralPoint q).im| ∧
        0 < xiSchwarzPairCompletedSourceWeylNormalizedIncrement q w n) := by
  by_cases hnormal : xiSchwarzPairSourceNormalCoefficient q = 0
  · exact Or.inl
      ((sourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate_nonempty_iff_normalCoefficient_eq_zero
        q p hd).2 hnormal)
  · right
    have him : (xiSpectralPoint q).im ≠ 0 := fun h => hnormal
      ((xiSchwarzPairSourceNormalCoefficient_eq_zero_iff q).2 h)
    intro n hn
    obtain ⟨w, hw, hH, hinc, _⟩ :=
      xiSchwarzPair_offLine_finiteDegree_nonlinearRenewal q him hn
    exact ⟨w, hw, hH, hinc, hinc.symm ▸ abs_pos.mpr him⟩

end

end RHTower
