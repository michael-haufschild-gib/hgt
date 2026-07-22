import GaloisForLFunctions.HTGeometry.FiniteReporterBoundedRecovery
import GaloisForLFunctions.RHTower.XiLogDerivReporterDataProcessing

/-!
# Bounded recovery of Xi logarithmic-derivative reporters

An exactly recoverable bounded recoding of a finite Xi reporter cannot arbitrarily attenuate its
surviving conditional-information values.  The recoder and recovery norms give a two-sided bound
at every derivative order.  This is the quantitative extension of the existing isometric Xi
recovery theorem.

The result does not repair the unconditional finite-reporter collapse: exact recovery returns the
original reporter, including its blind derivative direction.  Its positive content is uniform
quantitative transport of every value that the original observer algebra does retain.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions Module

/-- **Xi bounded-recovery information sandwich.**  A recoverable reporter recoding transports
every retained Xi conditional-information value with explicit condition-number control. -/
theorem xiLogDerivReporter_boundedRecovery_sandwich
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report) :
    ∀ N,
      HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
          (decode.toLinearMap.comp report) ≤
          ‖decode‖ ^ 2 *
            HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report ∧
        HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report ≤
          ‖recover‖ ^ 2 *
            HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
              (decode.toLinearMap.comp report) := by
  intro N
  exact HTGeometry.finiteDerivativeReporterConditionalInformation_boundedRecovery_sandwich
    N (logDeriv xi) report decode recover hrecover

/-- **Xi recoverable capacity-and-information profile.**  At every jet resolution, exact
recovery preserves the complete visible/blind coefficient census, while decoder and recovery
norms bound the distortion of retained Xi conditional information. -/
theorem xiLogDerivReporter_recoverableCapacityAndInformationProfile
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report) :
    ∀ N,
      Module.finrank ℂ (LinearMap.range
          (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi)
            (decode.toLinearMap.comp report))) =
          Module.finrank ℂ (LinearMap.range
            (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) ∧
        LinearMap.ker (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi)
            (decode.toLinearMap.comp report)) =
          LinearMap.ker
            (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report) ∧
        HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
            (decode.toLinearMap.comp report) ≤
          ‖decode‖ ^ 2 *
            HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report ∧
        HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report ≤
          ‖recover‖ ^ 2 *
            HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
              (decode.toLinearMap.comp report) := by
  intro N
  exact HTGeometry.finiteDerivativeReporter_recoverableCapacityAndInformationProfile
    N (logDeriv xi) report decode recover hrecover

/-- A uniform recovery-norm bound gives a uniform lower transport bound throughout the Xi
conditional-information tower. -/
theorem xiLogDerivReporter_div_recovery_bound_le
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report)
    {C : ℝ} (hC : 0 < C) (hrecoverNorm : ‖recover‖ ≤ C) :
    ∀ N,
      HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report /
          C ^ 2 ≤
        HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
          (decode.toLinearMap.comp report) := by
  intro N
  exact HTGeometry.finiteDerivativeReporterConditionalInformation_div_recovery_bound_le
    N (logDeriv xi) report decode recover hrecover hC hrecoverNorm

end

end RHTower
