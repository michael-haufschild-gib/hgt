import GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery
import GaloisForLFunctions.RHTower.XiLogDerivFiniteSpectralDressing
import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic

/-!
# Isometric recovery does not repair Xi reporter blindness

An isometric downstream encoding preserves every finite Xi reporter information value and is
exactly decoded by its Hilbert adjoint.  Nevertheless, the unconditional finite-dimensional Xi
reporter collapse remains: perfect recovery returns the original reporter, including its blind
direction, rather than recovering the derivative information erased before the encoding.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions Module

/-- Isometric postprocessing preserves the complete Xi conditional-information tower and admits
the adjoint as an exact reporter recovery. -/
theorem xiLogDerivReporter_isometric_information_and_recovery
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    (∀ N,
      HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
          (decode.toLinearMap.comp report) =
        HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report) ∧
    decode.toContinuousLinearMap.adjoint.toLinearMap.comp
        (decode.toLinearMap.comp report) = report := by
  exact ⟨fun N =>
      HTGeometry.finiteDerivativeReporterConditionalInformation_postcomp_linearIsometry
        N (logDeriv xi) report decode,
    HTGeometry.finiteDerivativeReporter_isometricAdjointRecovery report decode⟩

/-- **Perfectly recoverable reporter, irrecoverable source direction.**  At the unconditional Xi
collapse order, the isometric encoding has the same zero information and its adjoint recovers the
original reporter exactly, while the source derivative remains independent of all predecessors. -/
theorem exists_xiLogDeriv_isometricReporterRecovery_collapse
    (zeroIndex : ℕ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi)
        (decode.toLinearMap.comp report) = 0 ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi)) := by
  obtain ⟨k, hk, hzero, hpostzero, _, _, hrecover, hsource⟩ :=
    HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
      (HTGeometry.constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole
        (meromorphicAt_logDeriv_xi (xiZeroPoint zeroIndex))
        (meromorphicOrderAt_logDeriv_xi_eq_neg_one (xiZeroPoint_eq_zero zeroIndex)))
      report decode
  exact ⟨k, hk, hzero, hpostzero, hrecover, hsource⟩

/-- **Finite-Gibbs dressed Xi recovery boundary.**  Isometric postprocessing exactly recovers the
dressed reporter and preserves its zero-information witness, but cannot recover the same genuinely
new derivative direction erased before reporting. -/
theorem exists_xiLogDeriv_add_finiteGibbs_isometricReporterRecovery_collapse
    (zeroIndex : ℕ) {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) := by
  exact HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
    (xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      zeroIndex energy)
    report decode

end

end RHTower
