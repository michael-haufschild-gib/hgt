import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureFourierSourceAlias
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureRegularFiniteWindowSourceDecomposition

/-!
# Canonical phase-preserving HCF source decomposition

This module replaces the canonical `37 / 200 * L¹` Poisson-alias loss by the norm of the exact
nonzero Fourier alias.  Existing zero-free displacement data discharges source integrability at
every height, so the resulting pointwise majorant is unconditional and contains only pole--Gamma
source observables before divisor scalarization.

The new majorant connects directly to the strongest reflected three-center 75% receiver.  Its
nonzero-alias term retains oscillatory phase, making fixed-frequency explicit-formula cancellation
available; the previous absolute envelope erased that information.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Exact nonzero Fourier alias of the selected canonical pole--Gamma source. -/
def criticalFeatureCanonicalRegularNonzeroFourierAlias (n : ℕ) : ℂ :=
  criticalFeatureSourceNonzeroFourierAlias
    (volume.restrict (criticalFeatureCanonicalCore n))
    (criticalFeaturePositiveShiftPoleGammaDensity
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement)

/-- The canonical full-periodization error is exactly the phase-preserving source alias. -/
theorem ofReal_criticalFeatureCanonicalCoreFullPoleGammaObservable_sub_zeroMode_eq_alias
    (n : ℕ) :
    ((criticalFeatureCanonicalCoreFullPoleGammaObservable n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement -
      criticalFeatureCanonicalCorePoleGammaZeroMode n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement : ℝ) : ℂ) =
      criticalFeatureCanonicalRegularNonzeroFourierAlias n := by
  have h :=
    ofReal_integral_criticalFeatureRealBoundaryPeriodization_mul_sub_zeroMode_eq_alias
      (volume.restrict (criticalFeatureCanonicalCore n))
      (integrableOn_criticalFeatureCanonicalRegularPoleGammaDensity n)
  rw [criticalFeatureCanonicalCoreFullPoleGammaObservable,
    criticalFeatureCanonicalCorePoleGammaZeroMode,
    criticalFeatureFullLatticePoleGammaObservable,
    criticalFeaturePoleGammaZeroModeObservable]
  change
    (((∫ x in criticalFeatureCanonicalCore n,
        criticalFeatureRealBoundaryPeriodization x *
          criticalFeaturePositiveShiftPoleGammaDensity
            (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement x) -
      2 * Real.pi * ∫ x in criticalFeatureCanonicalCore n,
        criticalFeaturePositiveShiftPoleGammaDensity
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement x : ℝ) : ℂ) = _
  simpa only [criticalFeatureCanonicalRegularNonzeroFourierAlias] using h

theorem abs_criticalFeatureCanonicalCoreFullPoleGammaObservable_sub_zeroMode_eq_norm_alias
    (n : ℕ) :
    |criticalFeatureCanonicalCoreFullPoleGammaObservable n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement -
      criticalFeatureCanonicalCorePoleGammaZeroMode n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| =
      ‖criticalFeatureCanonicalRegularNonzeroFourierAlias n‖ := by
  calc
    |criticalFeatureCanonicalCoreFullPoleGammaObservable n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement -
      criticalFeatureCanonicalCorePoleGammaZeroMode n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| =
        ‖((criticalFeatureCanonicalCoreFullPoleGammaObservable n
            (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement -
          criticalFeatureCanonicalCorePoleGammaZeroMode n
            (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖criticalFeatureCanonicalRegularNonzeroFourierAlias n‖ :=
      congrArg norm
        (ofReal_criticalFeatureCanonicalCoreFullPoleGammaObservable_sub_zeroMode_eq_alias n)

/-- Finite-window core error bounded by the exact phase alias plus literal omitted centers. -/
theorem abs_criticalFeatureCanonicalRegularCoreFinitePoleGammaObservable_sub_zeroMode_le_phase
    (n : ℕ) :
    |criticalFeatureCanonicalCoreFinitePoleGammaObservable n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement -
      criticalFeatureCanonicalCorePoleGammaZeroMode n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| ≤
      ‖criticalFeatureCanonicalRegularNonzeroFourierAlias n‖ +
      |criticalFeatureCanonicalInteriorOmittedAlias n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| := by
  let eta :=
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
  have hid :
      criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta =
        (criticalFeatureCanonicalCoreFullPoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) -
        criticalFeatureCanonicalInteriorOmittedAlias n eta := by
    rw [criticalFeatureCanonicalInteriorOmittedAlias]
    ring
  rw [hid]
  exact (abs_sub _ _).trans
    (add_le_add
      (le_of_eq
        (abs_criticalFeatureCanonicalCoreFullPoleGammaObservable_sub_zeroMode_eq_norm_alias n))
      le_rfl)

/-- Unconditional canonical covariance bound retaining every nonzero Fourier phase. -/
theorem criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_le_phaseSourcePieces
    (n : ℕ) :
    criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance n ≤
      (criticalFeaturePoleGammaLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n) -
        criticalFeatureCanonicalCorePoleGammaZeroMode n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) +
      ‖criticalFeatureCanonicalRegularNonzeroFourierAlias n‖ +
      |criticalFeatureCanonicalInteriorOmittedAlias n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| +
      |criticalFeatureCanonicalExteriorPoleGammaTail n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| := by
  let eta :=
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
  let cutoff :=
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
  have hcore :=
    abs_criticalFeatureCanonicalRegularCoreFinitePoleGammaObservable_sub_zeroMode_le_phase n
  have hid :
      criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance n =
        (criticalFeaturePoleGammaLatticeBudget
            (criticalFeatureCanonicalLatticeWindow n) -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) -
        (criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) -
        criticalFeatureCanonicalExteriorPoleGammaTail n cutoff eta := by
    rw [criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance,
      criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance,
      criticalFeatureCanonicalExteriorPoleGammaTail]
    ring
  rw [hid]
  have hcoreNeg :
      -(criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) ≤
        |criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta| :=
    neg_le_abs _
  have htailNeg :
      -criticalFeatureCanonicalExteriorPoleGammaTail n cutoff eta ≤
        |criticalFeatureCanonicalExteriorPoleGammaTail n cutoff eta| :=
    neg_le_abs _
  have hcoreBound :
      -(criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) ≤
        ‖criticalFeatureCanonicalRegularNonzeroFourierAlias n‖ +
          |criticalFeatureCanonicalInteriorOmittedAlias n eta| :=
    hcoreNeg.trans hcore
  linarith

/-- Canonical source majorant with exact phase alias replacing the old `37 / 200 * L¹` term. -/
def criticalFeatureCanonicalRegularPhaseSourcePieceMajorant (n : ℕ) : ℝ :=
  (criticalFeaturePoleGammaLatticeBudget
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureCanonicalCorePoleGammaZeroMode n
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) +
  ‖criticalFeatureCanonicalRegularNonzeroFourierAlias n‖ +
  |criticalFeatureCanonicalInteriorOmittedAlias n
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| +
  |criticalFeatureCanonicalExteriorPoleGammaTail n
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement|

theorem criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_le_phaseSourcePieceMajorant
    (n : ℕ) :
    criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance n ≤
      criticalFeatureCanonicalRegularPhaseSourcePieceMajorant n := by
  simpa only [criticalFeatureCanonicalRegularPhaseSourcePieceMajorant] using
    criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_le_phaseSourcePieces n

theorem canonicalRegularLatticeSummedDisplacement_ceiling_of_phaseSourcePieceMajorant
    {c : ℝ}
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularPhaseSourcePieceMajorant c) :
    CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance c := by
  intro eps heps
  filter_upwards [hsource eps heps] with n hn
  exact
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_le_phaseSourcePieceMajorant
      n).trans hn

/-- Strongest phase-preserving source-to-75%-receiver connector. -/
theorem canonical_correctedBudget_ceiling_of_regularPhaseSourcePieceMajorant_reflectedDirectThreeCenter
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularPhaseSourcePieceMajorant (15872 / 21125)) :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125) := by
  apply
    canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_reflectedDirectThreeCenter.mpr
  exact
    (canonicalRegularLatticeSummedDisplacement_ceiling_iff_plemeljCovariance_ceiling
      (15872 / 21125)).mp
      (canonicalRegularLatticeSummedDisplacement_ceiling_of_phaseSourcePieceMajorant hsource)

end

end RHTower
